import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Optimizer
import Palamedes.Synthesizer.CGeneratorSearch
import Palamedes.Synthesizer.Totality
import Palamedes.Failure

open Lean Tactic Elab Meta Tactic

initialize
  registerTraceClass `palamedes.trace

register_option palamedes.debug : Bool := {
  defValue := false
  descr := "enable debug messages from palamedes"
}

/--
Pull the raw `Gen` out of a synthesized `CorrectGen` term by rewriting with the `extract` simp
set, which holds one `.val` equation per synthesis combinator. Unlike delta-reduction via
`withReducible (reduce ·)`, this unfolds exactly the combinator wrappers and nothing else, so
the combinators don't need to be `@[reducible]`.

Returns the extracted generator **and** the proof `e = extracted` that `simp` already computed. A
`none` from `simp` means it rewrote nothing, i.e. the two are syntactically equal, so `rfl` serves.
-/
def extractGen (e : Expr) : MetaM (Expr × Expr) := do
  let some ext ← getSimpExtension? `extract
    | throwError "simp extension `extract` not found"
  let ctx ← Simp.mkContext
    (config := { zetaDelta := true })
    (simpTheorems := #[← ext.getTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let (result, _) ← simp e ctx
  let proof ← match result.proof? with
    | some p => pure p
    | none => mkEqRefl e
  return (result.expr, proof)

/-- This is just a utility tactic for debugging. We don't call it in the real synthesizer. -/
elab "optimize_gen " t:term : tactic =>
  withMainContext do
    let m ← mkFreshExprMVar (some (.sort 0))
    let gen ← elabTerm t (some (.app (.const ``Palamedes.Gen []) m))
    let (gen', _) ← extractGen gen
    let (gen'', _) ← Palamedes.optimizeGen gen'
    let gen''' ← withReducible (reduce gen'')
    closeMainGoal `optimize_gen gen'''

/-- Run `tactic` against a fresh goal of type `goalType` and return the resulting term.

`TermElabM` rather than `TacticM` so that both front-ends can drive it: the `generator_search` tactic
lifts into it, and the `correct def` command — which has no surrounding tactic state at all — calls it
directly. -/
def solveGoalWithTactic (goalType : Expr) (tactic : TSyntax `tactic) : TermElabM Expr := do
  let m ← mkFreshExprMVar goalType
  let unsolved ← Tactic.run m.mvarId! (Tactic.evalTactic tactic)
  if unsolved.length > 0 then do
    throwError "goals left unsolved: {unsolved}"
  instantiateMVars m

/-- One run of the synthesis pipeline: search → extract → optimize → totality.

The pipeline used to compute three proofs and keep none of them. `CorrectGen.property`
(`cgen.val.support = P`), the extraction rewrite (`cgen.val = gen`), and the optimizer's
support-preservation proof (`support gen = support gen'`) each existed as a real proof term inside
`MetaM` and then went out of scope, so the fact the synthesizer exists to establish was proved and
discarded. They compose to `support gen' = P`, which is what `supportProof` carries. -/
structure SynthesisResult where
  /-- The optimized generator. -/
  gen : Expr
  /-- A proof of `Palamedes.Gen.support gen = P`, i.e. soundness and completeness against the
  target predicate. -/
  supportProof : Expr
  /-- A `Palamedes.Gen.total gen` witness, when the totality stage ran and succeeded. Since `total`
  is `Type`-valued this *is* the failure-free generator, not merely evidence that one exists —
  `.val.run` is a Basalt-shaped generator. `none` means the generator filters (or that the check
  was skipped). -/
  totalWitness? : Option Expr

/-- Run the shared pipeline against a predicate `pred : α → Prop`.

Both front-ends are thin packagings over this: they differ only in what they do with the result, not
in how it is computed. Totality failure is reported by a `none` witness rather than an exception, so
the caller decides whether that is a warning, an error, or a signal to emit the filtering form. -/
def runSynthesisPipeline (α pred : Expr) (checkTotal verbose : Bool) :
    TermElabM SynthesisResult := do
  -- 1. Search for an inhabitant of `CorrectGen pred`.
  let cgen ←
    try
      solveGoalWithTactic
        (mkAppN (.const ``Palamedes.CorrectGen []) #[α, pred])
        (← `(tactic| cgenerator_search))
    catch e =>
      throwError m!"Failed during generator synthesis.\n{e.toMessageData}"

  -- 2. Extract the raw `Gen`, keeping the rewrite that justifies it.
  -- Build the `Subtype` projections with the predicate given *explicitly*. `mkAppM ``Subtype.val`
  -- would have to see `CorrectGen P` as `Subtype ?p` to solve for `?p`, and `CorrectGen` is
  -- `@[implicit_reducible]` rather than `@[reducible]`, so `?p`
  -- can survive unassigned into the emitted proof. That is invisible until the kernel rejects the
  -- declaration for having metavariables, so name the argument rather than let it be inferred.
  let genTy := mkApp (Expr.const ``Palamedes.Gen []) α
  let subtypePred ← withLocalDeclD `g genTy fun g => do
    let body ← mkEq (← mkAppM ``Palamedes.Gen.support #[g]) pred
    mkLambdaFVars #[g] body
  let cgenVal ← mkAppOptM ``Subtype.val #[genTy, subtypePred, cgen]
  let cgenProp ← mkAppOptM ``Subtype.property #[genTy, subtypePred, cgen]
  let (gen, extractProof) ← extractGen cgenVal
  if verbose then
    logInfo m!"Synthesized generator:\n{(← ppExpr gen)}"

  -- 3. Optimize, keeping the support-preservation proof.
  let (gen', optProof) ←
    try
      Palamedes.optimizeGen gen
    catch e =>
      throwError m!"Failed during optimization.\n{e.toMessageData}"
  let gen'' ← withReducible (reduce gen')
  if verbose then
    logInfo m!"Optimized generator:\n{(← ppExpr gen'')}"

  -- Chain the three, right to left:
  --   support gen'  = support gen      (optimizer, flipped)
  --   support gen   = support cgen.val (extraction, flipped, under `support`)
  --   support cgen.val = pred          (the `CorrectGen` subtype's own property)
  let supportProof ← do
    let supportFn := mkApp (Expr.const ``Palamedes.Gen.support []) α
    let viaExtract ← mkEqSymm (← mkCongrArg supportFn extractProof)
    let chained ← mkEqTrans (← mkEqSymm optProof) (← mkEqTrans viaExtract cgenProp)
    -- `reduce` above produced a defeq but not syntactically equal term, so pin the statement to
    -- the generator actually being returned rather than the pre-reduction one.
    let stmt ← mkEq (← mkAppM ``Palamedes.Gen.support #[gen'']) pred
    -- Validate with `isDefEq` rather than `Meta.check`, matching `derive_tuning`'s `tuned_support`
    -- template. A full `check` re-typechecks simp's own proof term, and since Lean 4.33 compares
    -- types at `implicit` transparency, it rejects proofs whose predicate mentions
    -- a matcher where the statement mentions the underlying `casesOn` — defeq, but not at that
    -- transparency. `isDefEq` on the statement is the check that actually matters.
    unless ← isDefEq (← inferType chained) stmt do
      throwError "generator_search: the composed support proof does not match{indentExpr stmt}\n\
        proof has type{indentExpr (← inferType chained)}"
    mkExpectedTypeHint chained stmt

  -- 4. Totality: rebuild a `TGen` witness over the combinator spine.
  let totalWitness? ←
    if checkTotal then
      try
        pure <| some (← solveGoalWithTactic
          (← mkAppM ``Palamedes.Gen.total #[gen''])
          (← `(tactic| totality)))
      catch _ =>
        pure none
    else
      pure none

  return { gen := gen'', supportProof, totalWitness? }

/-- What the *declared return type* says the generator should be. Whether a generator filters is a
fact about its type, visible at every use site. -/
inductive Target where
  /-- `Palamedes.Gen α` — the synthesis-internal carrier. Total only; a filtering generator has to be
  declared in the Basalt shape, because `totalize`'s result is Basalt-shaped and `Fail` must not
  escape Palamedes. -/
  | palamedes (α : Expr)
  /-- `G α` for a Basalt `[Gen G]`. Emitted from the `TGen` witness, so it is `Fail`-free. -/
  | basalt (G α : Expr)
  /-- `G (Option α)` for a Basalt `[Gen G]`. Emitted via `totalize`: a failed guard is a `none`. -/
  | basaltOption (G α : Expr)

/-- The element type the predicate must range over. -/
def Target.elemType : Target → Expr
  | .palamedes α | .basalt _ α | .basaltOption _ α => α

/-- Elaborate `t` as a predicate `α → Prop`, returning `none` if it does not fit that type.

Used to *choose* between the total and filtering readings of a `G (Option β)` goal, so a failure here
is an ordinary control-flow outcome rather than an error to report. -/
private def elabPredAt? (t : Lean.Term) (α : Expr) : TermElabM (Option Expr) :=
  try
    Term.withoutErrToSorry do
      let e ← Term.elabTerm t (some (.forallE `a α (.sort 0) .default))
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      if e.hasSorry || e.hasExprMVar then return none
      return some e
  catch _ => return none

/-- Read the target off the goal type, and the predicate against it.

Dispatch is on the **predicate's** type, since `P : α → Prop` fixes `α` and a predicate genuinely
over `Option β` would otherwise be ambiguous with the filtering case. But it cannot simply *read*
`P`'s type first: `generator_search (· = 2)` has no type of its own and needs the goal to supply the
expected one. So the goal proposes `τ`, and only if `P` does not fit `τ → Prop` — and `τ` is
`Option β` — is the filtering reading tried. A predicate that really is over `Option β` fits the
first attempt and wins. -/
def classifyGoal (goalTy : Expr) (t : Lean.Term) : TermElabM (Target × Expr) := do
  match goalTy with
  | .app (.const ``Palamedes.Gen []) τ =>
    let some p ← elabPredAt? t τ
      | throwError "generator_search: the predicate must have type{indentExpr τ} → Prop"
    return (.palamedes τ, p)
  | .app carrier τ =>
    -- Basalt's `Gen` is universe-polymorphic, so an auto-bound `[Gen G]` binder elaborates `G` at
    -- `Type → Type ?u`. Palamedes' carrier is fixed at `Type → Type`, so pin the universe here,
    -- while `?u` is still unassigned — otherwise it only surfaces later as a mismatch inside the
    -- emitted `totalize`/`TGen.run` application, which reads as a bug in emission rather than a
    -- fact about the declared binder.
    let typeType ← mkArrow (mkSort Level.one) (mkSort Level.one)
    unless ← isDefEq (← inferType carrier) typeType do
      throwError "generator_search: the goal's type constructor{indentExpr carrier}\n\
        must have type `Type → Type`, but has{indentExpr (← inferType carrier)}"
    let some _ ← synthInstance? (← mkAppM ``_root_.Gen #[carrier])
      | throwError "generator_search: the goal's type constructor{indentExpr carrier}\n\
          is not a Basalt generator monad (no `Gen` instance), and the goal is not \
          `Palamedes.Gen α`"
    match τ with
    | .app (.const ``Option [_]) β =>
      -- Filtering reading first (see the docstring). Elaboration is too permissive to decide the
      -- other way round: `fun n => lo ≤ n ∧ n ≤ hi` typechecks at `Option Nat → Prop` too, because
      -- Mathlib gives `Option` an `LE` instance and silently coerces `lo` to `some lo`.
      if let some p ← elabPredAt? t β then
        return (.basaltOption carrier β, p)
      let some p ← elabPredAt? t τ
        | throwError "generator_search: the predicate fits neither{indentExpr β} → Prop\n\
            (a filtering generator) nor{indentExpr τ} → Prop (a total generator of options)"
      return (.basalt carrier τ, p)
    | _ =>
      let some p ← elabPredAt? t τ
        | throwError "generator_search: the predicate must have type{indentExpr τ} → Prop"
      return (.basalt carrier τ, p)
  | _ =>
    throwError "generator_search: the goal must be `G α`, `G (Option α)` for a Basalt \
      `[Gen G]`, or `Palamedes.Gen α`, got{indentExpr goalTy}"

/-- Turn a totality witness back into generator code.

The Basalt-shaped emission is `witness.val.run`. Left as-is that is a *proof term* — a tree of
`total_*` applications — which would make the emitted definition unreadable as a generator and hide
its choice sites from `derive_tuning`. Palamedes' whole output contract is that a synthesized
generator is a generator you can read, so the projection has to actually be performed.

Delta-unfolds exactly the witness constructors (the fixed combinator basis plus whatever the
`@[total]` registry holds, so a new datatype needs no edit here) and lets simp do the `.val`/`.run`
projections. Deliberately *not* a full `Meta.reduce`: that would also unfold Basalt's `frequency`
and `oneOf` into `frequencyAux`/`choose`, destroying exactly the structure we want to keep. -/
def extractWitness (e : Expr) : MetaM Expr := do
  let basis : Array Name := #[
    ``Palamedes.Gen.Total.total_pure, ``Palamedes.Gen.Total.total_bind,
    ``Palamedes.Gen.Total.total_pick, ``Palamedes.Gen.Total.total_oneOf,
    ``Palamedes.Gen.Total.total_frequency, ``Palamedes.Gen.Total.total_map,
    ``Palamedes.Gen.Total.total_dite,
    ``Palamedes.Gen.Total.totalList_nil, ``Palamedes.Gen.Total.totalList_cons,
    ``Palamedes.Gen.Total.totalWeighted_nil, ``Palamedes.Gen.Total.totalWeighted_cons,
    ``Palamedes.TGen.pure, ``Palamedes.TGen.bind, ``Palamedes.TGen.pick,
    ``Palamedes.TGen.frequency, ``Palamedes.TGen.map, ``Palamedes.TGen.toGen]
  let names := basis ++ Palamedes.totalLemmas (← getEnv)
  -- Start from the `twitness` set (the `.val`/`.run` equations, including the one that pushes `.val`
  -- through the `Eq.rec` the totality tactic's `split` leaves around each match arm), then add the
  -- constructors to delta-unfold. `List.map_cons`/`_nil` are needed so the branch lists of a
  -- `frequency` actually compute — otherwise `.run` stays stuck under a `List.map` lambda.
  let some twExt ← getSimpExtension? `twitness
    | throwError "simp extension `twitness` not found"
  let mut thms ← twExt.getTheorems
  for n in names do
    thms ← thms.addDeclToUnfold n
  let ctx ← Simp.mkContext
    (config := { proj := true, zetaDelta := true })
    (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simp e ctx
  return r.expr

/-- Package the pipeline's result at the shape the declaration asked for.

This is the whole of "Basalt owns the vocabulary": the pipeline is identical in every case and only
the final packaging differs. -/
def packageFor (target : Target) (res : SynthesisResult) (report : MessageData → TermElabM Unit) :
    TermElabM Expr := do
  match target with
  | .palamedes _ =>
    if res.totalWitness?.isNone then
      report m!"this generator filters: a `Gen.assume` survived optimization, so it can fail when \
        sampled. Declare it as `[Gen G] → G (Option _)` to reflect that in the type."
    return res.gen
  | .basalt G α =>
    let some w := res.totalWitness?
      | throwError "generator_search: this generator filters — a `Gen.assume` survived \
          optimization — so it cannot be emitted at{indentExpr (mkApp G α)}, which is `Fail`-free \
          by construction.\n\nDeclare it as `G (Option _)` instead, so the type reflects that it \
          can fail."
    let tgen ← mkAppOptM ``Subtype.val #[none, none, w]
    extractWitness (← mkAppOptM ``Palamedes.TGen.run #[some α, some tgen, some G, none])
  | .basaltOption G α =>
    if res.totalWitness?.isSome then
      report m!"this generator never fails, so the `Option` is not needed — `{← ppExpr (mkApp G α)}` will do."
    mkAppOptM ``Palamedes.Gen.totalize #[some α, some res.gen, some G, none]

def generatorSearchElab
    (stx : Syntax)
    (t : Lean.Term)
    (tryThis : Bool) :
    TacticM Unit := do
  let opts ← getOptions
  let verbose := palamedes.debug.get opts

  let g ← getMainGoal
  let goalTy ← instantiateMVars (← g.getType)
  let (target, mpred) ← classifyGoal goalTy t
  let α := target.elemType

  if verbose then do
    TryThis.addSuggestion stx
      s!"-- generator_search ({← ppExpr mpred})
  let cg : CorrectGen ({← ppExpr mpred}) := by
    cgenerator_search
  let g : Gen ({← ppExpr α}) := by
    optimize_gen cg.val
  let _ : Gen.total g := by
    totality
  exact g"

  let prettyPred ←
    try
      lambdaBoundedTelescope mpred 1 fun fvs body =>
        let a := fvs[0]!
        let subst := FVarSubst.empty
        let tgt := Expr.fvar (FVarId.mk `TARGET)
        return (subst.insert a.fvarId! tgt).apply body
    catch _ =>
      pure mpred

  withTraceNode `palamedes.trace (fun _ => pure m!"⟪{α}⟫⟪{prettyPred}⟫") do

  -- Totality is always checked: the declared type says whether the generator may filter, and
  -- totality is how that claim is verified. (Distinct from almost-sure termination, which is
  -- orthogonal and which nothing here establishes.)
  let res ← runSynthesisPipeline α mpred true verbose
  let emitted ← packageFor target res (fun msg => logWarning msg)

  if tryThis then
    withOptions ((pp.proofs.set · true) ∘ (pp.fieldNotation.generalized.set · false)) do
      TryThis.addExactSuggestion stx emitted

  closeMainGoal `generator_search emitted

/--
`generator_search P` closes a generator goal with a generator whose *support* is exactly `P` — it can
produce every value satisfying `P`, and nothing else. `P` may be a `Prop`-valued predicate or a
decidable `α → Bool`, including a recursive one over any `derive_palamedes`d datatype.

**The declared return type chooses the shape**, and is dispatched on the predicate's type:

```lean
def genEq2 [Gen G] : G Nat := by generator_search (· = 2)              -- total
def genRBT [Gen G] : G (Option (Tree Nat)) := by generator_search isRBT -- filtering
def genEq2' : Palamedes.Gen Nat := by generator_search (· = 2)          -- synthesis-internal carrier
```

Whether a generator can fail is a fact about its type, visible at every use site:

| totality | declared | result |
|---|---|---|
| succeeds | `G α` | emitted from the `TGen` witness |
| fails | `G (Option α)` | emitted via `totalize` |
| fails | `G α` | **error** — declare `G (Option α)` |
| succeeds | `G (Option α)` | warning — it never fails, `G α` will do |

Row 3 is an *error* rather than the warning it is for a `Palamedes.Gen α` goal, and that asymmetry is
forced: `G α` is `Fail`-free by construction, so there is simply no term to emit. For the internal
`Palamedes.Gen α` carrier there is one — it just filters — so that case warns and proceeds.

A synthesized generator ships uniform, which diverges for a static- or growing-seed generator like
`genWellTyped`. To weight it, run `derive_tuning` on it and sample `<gen>.tuned θ` at a `Tuning`
(e.g. `SchedulePolicy.stlc.materialize <gen>.sites`). Support is unaffected by the weighting.
-/
syntax (name := generatorSearch) "generator_search " term : tactic

@[tactic generatorSearch]
def expandGeneratorSearch : Tactic := fun stx => do
  match stx with
  | `(tactic| generator_search $t) => generatorSearchElab stx t false
  | _ => throwError "invalid syntax"

/-- `generator_search?` is `generator_search` (same modifiers, same result) that additionally emits
the synthesized generator as a "Try this" suggestion, so the term can be pasted in place of the
tactic call. Useful for inspecting what the search actually produced. -/
syntax (name := generatorSearch?) "generator_search? " term : tactic

@[tactic generatorSearch?]
def expandGeneratorSearch? : Tactic := fun stx => do
  match stx with
  | `(tactic| generator_search? $t) => generatorSearchElab stx t true
  | _ => throwError "invalid syntax"
