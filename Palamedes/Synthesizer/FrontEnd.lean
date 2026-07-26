/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.PGen
import Palamedes.CorrectGen
import Palamedes.Optimizer
import Palamedes.Synthesizer.CGeneratorSearch
import Palamedes.Synthesizer.Totality
import Palamedes.Failure
import Palamedes.Tuning

/-!
# The `generator_search` front-end

The user-facing pipeline: search (`cgenerator_search`) → extract a raw `PGen` → optimize → rebuild
a totality witness → package at the declared shape (`G α` from the `TGen` witness, `G (Option α)`
via `totalize`, or the `Palamedes.PGen` carrier directly). `runSynthesisPipeline` is the shared
core; the `@[correct]` attribute (`Correct.lean`) reads the proofs it leaves behind.
-/

open Lean Tactic Elab Meta Tactic

initialize
  registerTraceClass `palamedes.trace

register_option palamedes.debug : Bool := {
  defValue := false
  descr := "enable debug messages from palamedes"
}

/--
Pull the raw `PGen` out of a synthesized `CorrectGen` term by rewriting with the `extract` simp
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
    let gen ← elabTerm t (some (.app (.const ``Palamedes.PGen []) m))
    let (gen', _) ← extractGen gen
    let (gen'', _) ← Palamedes.optimizeGen gen'
    let gen''' ← withReducible (reduce gen'')
    closeMainGoal `optimize_gen gen'''

/-- Run `tactic` against a fresh goal of type `goalType` and return the resulting term.

`TermElabM` rather than `TacticM` so that every caller can drive it: the `generator_search` tactic
lifts into it, and `@[correct]` — which runs after elaboration, with no tactic state around it at
all — calls it directly to discharge the filtering path's `someSupport` bridge. -/
def solveGoalWithTactic (goalType : Expr) (tactic : TSyntax `tactic) : TermElabM Expr := do
  let m ← mkFreshExprMVar goalType
  let unsolved ← Tactic.run m.mvarId! (Tactic.evalTactic tactic)
  if unsolved.length > 0 then do
    throwError "goals left unsolved: {unsolved}"
  instantiateMVars m

/-- `solveGoalWithTactic`, but *running to completion and leaving goals* is reported as the leftover
goals rather than as an exception.

The distinction matters wherever an unclosed goal is itself a meaningful answer. Catching the
exception instead would lump it together with the tactic *throwing* — a heartbeat blowout, a
missing registry entry, an interrupt — which are not answers about the goal at all. Only the
totality stage needs this today; see `runSynthesisPipeline`, which reads the leftover goals to say
*which* head it could not reconstruct. -/
def solveGoalWithTactic? (goalType : Expr) (tactic : TSyntax `tactic) :
    TermElabM (Except (List MVarId) Expr) := do
  let m ← mkFreshExprMVar goalType
  let unsolved ← Tactic.run m.mvarId! (Tactic.evalTactic tactic)
  if unsolved.length > 0 then return .error unsolved
  return .ok (← instantiateMVars m)

/-- The head constants a totality goal is stuck on: those with no `@[total]` rule.

This is the diagnostic payoff of keying the descent on the head. `totality` is `repeat' first | …`,
which never fails, so an unclosed goal carries no information about *why* on its own — but a
dispatch table can simply be asked which heads it has no rule for. -/
def totalityGaps (goals : List MVarId) : MetaM (Array Name) := do
  let table := Palamedes.totalTable (← getEnv)
  let mut gaps := #[]
  for g in goals do
    if ← g.isAssigned then continue
    let some key ← g.withContext do Palamedes.totalKey? (← instantiateMVars (← g.getType))
      | continue
    unless table.contains key || gaps.contains key.2 do
      gaps := gaps.push key.2
  return gaps

/-- One run of the synthesis pipeline: search → extract → optimize → totality.

Three proofs arise along the way and compose to `support gen' = P`: `CorrectGen.property`
(`cgen.val.support = P`), the extraction rewrite (`cgen.val = gen`), and the optimizer's
support-preservation proof (`support gen = support gen'`). That composite is what `supportProof`
carries, so the fact the synthesizer exists to establish outlives the `MetaM` that computed it. -/
structure SynthesisResult where
  /-- The optimized generator. -/
  gen : Expr
  /-- A proof of `Palamedes.PGen.support gen = P`, i.e. soundness and completeness against the
  target predicate. -/
  supportProof : Expr
  /-- A `Palamedes.PGen.total gen` witness, when the totality stage ran and succeeded. Since `total`
  is `Type`-valued this *is* the failure-free generator, not merely evidence that one exists —
  `.val.run` is a Basalt-shaped generator.

  `none` on its own does **not** mean the generator filters; read `totalityFailure?` too. -/
  totalWitness? : Option Expr
  /-- Why there is no witness, when the reason was not "the generator filters". -/
  totalityFailure? : Option MessageData
  /-- Heads the descent had no `@[total]` rule for, read off the goals it left. Empty when the
  witness succeeded or when the tactic threw. -/
  totalityGaps : Array Name := #[]
  /-- The `frequency` sites `installTuning` created, when a `Tuning` binder was threaded. Empty when
  the generator was left uniform. -/
  sites : Array Palamedes.TuningSiteInfo := #[]

/-- Run the shared pipeline against a predicate `pred : α → Prop`.

Callers are thin packagings over this: they differ only in what they do with the result, not in how
it is computed. Totality failure is reported by a `none` witness rather than an exception, so the
caller decides whether that is a warning, an error, or a signal to emit the filtering form.

`θ?` is the declaration's `Tuning` binder, when it has one. Tuning runs here rather than after the
fact because everything downstream — the totality witness, the packaging, the law — should be about
the *tuned* generator, and there should only ever be one of them. See `Palamedes/Tuning.lean`. -/
def runSynthesisPipeline (α pred : Expr) (checkTotal verbose : Bool)
    (θ? : Option Expr := none) (declName : Name := `_gen) :
    TermElabM SynthesisResult := do
  -- 1. Search for an inhabitant of `CorrectGen pred`.
  let cgen ←
    try
      solveGoalWithTactic
        (mkAppN (.const ``Palamedes.CorrectGen []) #[α, pred])
        (← `(tactic| cgenerator_search))
    catch e =>
      throwError m!"Failed during generator synthesis.\n{e.toMessageData}"

  -- 2. Extract the raw `PGen`, keeping the rewrite that justifies it.
  -- Build the `Subtype` projections with the predicate given *explicitly*. `mkAppM ``Subtype.val`
  -- would have to see `CorrectGen P` as `Subtype ?p` to solve for `?p`, and `CorrectGen` is
  -- `@[implicit_reducible]` rather than `@[reducible]`, so `?p`
  -- can survive unassigned into the emitted proof. That is invisible until the kernel rejects the
  -- declaration for having metavariables, so name the argument rather than let it be inferred.
  let genTy := mkApp (Expr.const ``Palamedes.PGen []) α
  let subtypePred ← withLocalDeclD `g genTy fun g => do
    let body ← mkEq (← mkAppM ``Palamedes.PGen.support #[g]) pred
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

  -- 3b. Tuning: thread the declaration's `Tuning` binder through every choice site.
  --
  -- Before totality, deliberately: the witness, the packaging and the emitted law must all be about
  -- the generator the user actually gets, and running this afterwards would mean rebuilding each of
  -- them against a second, separately-tuned generator. `total_frequency` never inspects weights, so
  -- stage 4 closes exactly as it would for the uniform generator.
  let (gen''', tuneProof?, sites) ←
    match θ? with
    | none => pure (gen'', none, #[])
    | some θ =>
      try
        let r ← Palamedes.installTuning declName θ gen''
        if verbose then
          logInfo m!"Tuned generator ({r.sites.size} sites):\n{(← ppExpr r.gen)}"
        pure (r.gen, r.supportProof?, r.sites)
      catch e =>
        throwError m!"Failed while installing tuning.\n{e.toMessageData}"

  -- Chain, right to left:
  --   support gen'' = support gen'     (tuning, flipped; absent when no site fired)
  --   support gen'  = support gen      (optimizer, flipped)
  --   support gen   = support cgen.val (extraction, flipped, under `support`)
  --   support cgen.val = pred          (the `CorrectGen` subtype's own property)
  let supportProof ← do
    let supportFn := mkApp (Expr.const ``Palamedes.PGen.support []) α
    let viaExtract ← mkEqSymm (← mkCongrArg supportFn extractProof)
    let chained ← mkEqTrans (← mkEqSymm optProof) (← mkEqTrans viaExtract cgenProp)
    let chained ← match tuneProof? with
      | none => pure chained
      | some p => mkEqTrans (← mkEqSymm p) chained
    -- `reduce` above produced a defeq but not syntactically equal term, so pin the statement to
    -- the generator actually being returned rather than the pre-reduction one.
    let stmt ← mkEq (← mkAppM ``Palamedes.PGen.support #[gen''']) pred
    -- Validate with `isDefEq` rather than `Meta.check`. A full `check` re-typechecks simp's own
    -- proof term, and since Lean 4.33 compares
    -- types at `implicit` transparency, it rejects proofs whose predicate mentions
    -- a matcher where the statement mentions the underlying `casesOn` — defeq, but not at that
    -- transparency. `isDefEq` on the statement is the check that actually matters.
    unless ← isDefEq (← inferType chained) stmt do
      throwError "generator_search: the composed support proof does not match{indentExpr stmt}\n\
        proof has type{indentExpr (← inferType chained)}"
    mkExpectedTypeHint chained stmt

  -- 4. Totality: rebuild a `TGen` witness over the combinator spine.
  --
  -- Three outcomes, kept apart. A witness is success. The tactic running to completion and leaving
  -- goals is the designed "this generator filters" signal. The tactic *throwing* is neither — it is
  -- a gap in the reconstruction basis, and reporting it as a filter would send the user to add an
  -- `Option` their generator does not need (and `totalize` would accept, silently, forever).
  let mut totalWitness? : Option Expr := none
  let mut totalityFailure? : Option MessageData := none
  let mut gaps : Array Name := #[]
  if checkTotal then
    try
      match ← solveGoalWithTactic?
          (← mkAppM ``Palamedes.PGen.total #[gen'''])
          (← `(tactic| totality)) with
      | .ok w => totalWitness? := some w
      | .error unsolved => gaps ← totalityGaps unsolved
    catch e =>
      -- Never a statement about the generator: rethrow rather than record. `catch _` here would
      -- turn a Ctrl-C into "your generator filters".
      if e.isInterrupt || e.isMaxHeartbeat || e.isMaxRecDepth then throw e
      totalityFailure? := some e.toMessageData

  return { gen := gen''', supportProof, totalWitness?, totalityFailure?, totalityGaps := gaps,
           sites }

/-- What the *declared return type* says the generator should be. Whether a generator filters is a
fact about its type, visible at every use site. -/
inductive Target where
  /-- `Palamedes.PGen α` — the synthesis-internal carrier. Total only; a filtering generator has to be
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

/-! ## The synthesis stash

`generator_search` proves `support gen = P` and then closes a goal; the theorem it could state about
the declaration cannot be added yet, because during the tactic that declaration does not exist. The
`@[correct]` attribute (`Synthesizer/Correct.lean`) runs *after* it does, so the tactic leaves the
proof here and the attribute picks it up.

Ordering is the only obstacle: `Term.getDeclName?` already supplies a tactic the name it is
elaborating into, and an attribute at `applicationTime := .afterCompilation` is exactly the tool for
adding a declaration once that name exists. Lean keeps ownership of binder elaboration, auto-bound
implicits and universes.
-/

/-- Which declared shape a stashed synthesis was run at. `Target` cannot be stored as-is: it holds
`Expr`s referring to binders that are out of scope by the time the attribute runs, and both of them
(`G` and `α`) are recoverable from the finished constant's type. -/
inductive Shape where
  | palamedes | basalt | basaltOption
  deriving Inhabited, BEq

def Target.shape : Target → Shape
  | .palamedes _ => .palamedes
  | .basalt _ _ => .basalt
  | .basaltOption _ _ => .basaltOption

/-- What `generator_search` leaves for `@[correct]`.

Every field is **closed over the declaration's binder telescope** (`fun xs => …`) and
**metavariable-free**. Both are load-bearing: the attribute runs in a fresh `MetaM` where neither the
tactic's local context nor its metavariable context exists, so an open term's `fvar`s are dangling
and a surviving mvar surfaces there as `unknown universe metavariable ?_uniq.N` reported against the
`def` — with no `?m` visible anywhere in it. `stashSynthesis` therefore checks rather than assumes. -/
structure SynthesisStash where
  /-- The declared shape, which chooses which law is emitted. -/
  shape : Shape
  /-- `fun xs => P`, the predicate the support was proved equal to. -/
  pred : Expr
  /-- `fun xs => gen`, the optimized `PGen` carrier. The Basalt shapes are projections of this, and
  the filtering law's `someSupport` bridge is discharged against it. -/
  gen : Expr
  /-- `fun xs => (h : PGen.support gen = P)`. -/
  supportProof : Expr
  /-- `fun xs => (w : PGen.total gen)`, when the totality stage produced one. -/
  totalWitness? : Option Expr

initialize synthesisExt : EnvExtension (NameMap SynthesisStash) ←
  registerEnvExtension (pure {})

/-- The binders of the declaration currently being elaborated, as they stand at the tactic's site.

The recursive self-reference is in scope too (`genFoo : ℕ → ℕ → PGen α`), flagged `isAuxDecl`.
Dropping it and any implementation detail leaves exactly the telescope
`forallTelescope ci.type` yields once the constant exists, **in the same order** — including
auto-bound implicits, so the idiomatic `[Gen G]` spelling with `G` never written lines up too. That
positional correspondence is what lets the attribute re-open a stashed `fun xs => _` with `.beta`. -/
def declBinders : MetaM (Array Expr) := do
  let mut xs := #[]
  for d? in (← getLCtx).decls do
    if let some d := d? then
      unless d.isAuxDecl || d.isImplementationDetail do
        xs := xs.push d.toExpr
  return xs

/-- The declaration's `Tuning` binder, if it declared one.

**The signature says whether a generator is tunable**, the same way it already says whether one can
filter. A `θ : Tuning` binder in scope is threaded through every choice site; no binder means the
generator ships uniform. There is deliberately no flag and no warning — declining to be tunable is a
legitimate thing for a signature to say, and `.uniform` makes the binder free to add later.

The first such binder wins; a second is ignored rather than rejected, since nothing here can tell
which one a user meant and a generator wanting two tunings is not a thing the pass can express. -/
def declTuningBinder? : MetaM (Option Expr) := do
  for x in ← declBinders do
    if (← whnf (← inferType x)).isConstOf ``Tuning then return some x
  return none

/-- Record a completed synthesis for `@[correct]`, if we are elaborating into a named declaration.

A `nothing to stash` outcome is silent and normal: `generator_search` inside an `example`, a `have`,
or a term-level `by` block has no declaration to state a law about. `@[correct]` on such a
declaration is what reports the absence, since that is where it is a mistake. -/
def stashSynthesis (target : Target) (pred : Expr) (res : SynthesisResult) : TermElabM Unit := do
  let some declName ← Term.getDeclName? | return
  let xs ← declBinders
  let close (e : Expr) : TermElabM Expr := do
    let e ← instantiateMVars (← mkLambdaFVars xs (← instantiateMVars e))
    if e.hasExprMVar || e.hasLevelMVar then
      throwError "generator_search: the proof stashed for `{declName}` still has metavariables \
        after instantiation{indentExpr e}\n\n\
        This is a bug in the synthesizer rather than in the declaration: `@[correct]` runs in a \
        fresh elaboration context, so anything left unassigned here has no way to be solved there."
    return e
  let stash : SynthesisStash := {
    shape := target.shape
    pred := ← close pred
    gen := ← close res.gen
    supportProof := ← close res.supportProof
    totalWitness? := ← res.totalWitness?.mapM close }
  modifyEnv (synthesisExt.modifyState · (·.insert declName stash))

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
  | .app (.const ``Palamedes.PGen []) τ =>
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
    let some _ ← synthInstance? (← mkAppM ``Gen #[carrier])
      | throwError "generator_search: the goal's type constructor{indentExpr carrier}\n\
          is not a Basalt generator monad (no `Gen` instance), and the goal is not \
          `Palamedes.PGen α`"
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
      `[Gen G]`, or `Palamedes.PGen α`, got{indentExpr goalTy}"

/-- Drop the proof transports that are the identity.

A floated `assume` reaches this stage as a `dite` whose branches bind its guard, and rewriting
*underneath* those branches means going through Lean's `dite` congruence, which transports the bound
proof into each arm. The transport is emitted whether or not the guard itself was rewritten; when it
was not, the equation it transports along is `rfl` and the wrapper denotes nothing. Nothing
downstream removes it — `simp` never revisits proof subterms, and `Meta.reduce` skips proofs — so
every side-condition proof in the emitted generator ends up wrapped in an `Eq.mpr_prop (Eq.refl …)`.

The cost is not only noise. A primitive's side-condition delaborator (`delabChoose`,
`delabElements`) drops the proof only when `isAuxProofOverLocals` can see that it is applied to a
local hypothesis — the guard. Wrapped, the guard is not an argument by inspection, so the proof
prints in full and the emitted term stops being pasteable. `genWellTyped`'s `elements` draws are
where that shows, being the ones whose data argument is computed rather than a binder.

Replacing `Eq.mpr_prop h₁ h₂` by `h₂` is type-correct exactly when the two `Prop`s are defeq, which
is what is checked; proof irrelevance does the rest. -/
private def dropIdentityTransports (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    let_expr Eq.mpr_prop p q _ h := e | return .continue
    if ← withNewMCtxDepth (isDefEq p q) then return .continue h else return .continue)

/-- Turn a totality witness back into generator code.

The Basalt-shaped emission is `witness.val.run`. Left as-is that is a *proof term* — a tree of
`total_*` applications — which would make the emitted definition unreadable as a generator and hide
its choice sites from the tuning pass. Palamedes' whole output contract is that a synthesized
generator is a generator you can read, so the projection has to actually be performed.

Delta-unfolds exactly the witness constructors (the fixed combinator basis plus whatever the
`@[total]` registry holds, so a new datatype needs no edit here) and lets simp do the `.val`/`.run`
projections. Deliberately *not* a full `Meta.reduce`: that would also unfold Basalt's `frequency`
and `oneOf` into `frequencyAux`/`choose`, destroying exactly the structure we want to keep. -/
def extractWitness (e : Expr) : MetaM Expr := do
  -- The witness constructors are exactly the `@[total]` registry — the generic basis included, since
  -- it is registered the same way — so the rest is the `TGen` combinators they build with.
  let names := Palamedes.tgenBasis ++ Palamedes.totalLemmas (← getEnv)
  -- Start from the `totality_witness` set (the `.val`/`.run` equations, including the one that pushes `.val`
  -- through the `Eq.rec` the totality tactic's `split` leaves around each match arm), then add the
  -- constructors to delta-unfold. `List.map_cons`/`_nil` are needed so the branch lists of a
  -- `frequency` actually compute — otherwise `.run` stays stuck under a `List.map` lambda.
  let some twExt ← getSimpExtension? `totality_witness
    | throwError "simp extension `totality_witness` not found"
  let mut thms ← twExt.getTheorems
  for n in names do
    thms ← thms.addDeclToUnfold n
  let ctx ← Simp.mkContext
    (config := { proj := true, zetaDelta := true })
    (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simp e ctx
  dropIdentityTransports r.expr

/-- Why the totality stage produced no witness, as far as the evidence actually supports. -/
inductive TotalityDiagnosis where
  /-- The generator genuinely filters: an `assume` is present and reconstruction stopped at it. -/
  | filters
  /-- Reconstruction could not cover this generator, which is a fact about the *basis*, not about
  the generator. Carries the underlying error when the tactic threw rather than left goals, and the
  heads it had no rule for when it left them. -/
  | gap (err? : Option MessageData) (gaps : Array Name)

/-- Distinguish a genuine filter from a gap in the reconstruction basis.

Two signals, because neither alone is enough:

* The tactic **throwing** is never an answer about the generator (an error inside a registry lemma,
  say). `totalityFailure?` records those.
* The tactic **leaving goals** is the designed filter signal — but only if there is something to
  filter on. `totality` is `repeat' first | …`, and `repeat'` does not fail, so a datatype with no
  `@[total]` lemma also just leaves goals. That is the common registry gap, and it is
  indistinguishable from a filter by control flow alone.

So check the term: `PGen.assume` is the only thing a generator can fail at, and the optimizer floats
every *satisfiable* one out. No `assume` anywhere means "it filters" is not a claim the evidence
supports, whatever the tactic did.

Erring toward `.gap` only ever changes the wording of a message, never whether one is emitted, so a
term whose `assume` is somehow hidden behind an un-unfolded constant costs a confusing sentence
rather than a wrong outcome. -/
def diagnoseTotality (res : SynthesisResult) : TotalityDiagnosis :=
  match res.totalityFailure? with
  | some err => .gap (some err) res.totalityGaps
  | none =>
    if (res.gen.find? (·.isConstOf ``Palamedes.PGen.assume)).isSome then .filters
    else .gap none res.totalityGaps

/-- The shared explanation for a reconstruction gap: what it is, and what not to do about it. -/
def gapMessage (err? : Option MessageData) (gaps : Array Name := #[]) : MessageData :=
  let cause := match err?, gaps.toList with
    | some err, _ => m!"Totality reconstruction errored rather than simply not applying. The \
        underlying error was:{indentD err}"
    -- The descent dispatches each node on its head constant, so an unclosed goal names the head it
    -- had no rule for. Before that it could only guess, since `repeat' first | …` never fails.
    | none, (_ :: _) => m!"Totality reconstruction has no `@[total]` rule for \
        {MessageData.andList (gaps.toList.map (m!"`{·}`"))}, so it could not descend past \
        {if gaps.size == 1 then "that node" else "those nodes"}."
    | none, [] => m!"Totality reconstruction left goals unclosed, but the generator contains no \
        `PGen.assume` — so there is nothing in it that can fail, and the usual cause is a datatype \
        with no `@[total]` lemma registered."
  m!"{cause}\n\nThis is a gap in the reconstruction basis, **not** evidence that the generator \
    filters. Declaring it at `G (Option _)` would compile — `totalize` accepts any generator — but \
    it would bury the gap behind an `Option` the generator does not need, and weaken the emitted \
    law from `IsSoundAndComplete` to `IsSomeSoundAndComplete`. Fix the registration instead."

/-- Package the pipeline's result at the shape the declaration asked for.

This is the whole of "Basalt owns the vocabulary": the pipeline is identical in every case and only
the final packaging differs. -/
def packageFor (target : Target) (res : SynthesisResult) (report : MessageData → TermElabM Unit) :
    TermElabM Expr := do
  match target with
  | .palamedes _ =>
    if res.totalWitness?.isNone then
      match diagnoseTotality res with
      | .filters =>
        report m!"this generator filters: a `PGen.assume` survived optimization, so it can fail when \
          sampled. Declare it as `[Gen G] → G (Option _)` to reflect that in the type."
      | .gap err? gaps =>
        report m!"could not reconstruct a totality witness.\n\n{gapMessage err? gaps}"
    return res.gen
  | .basalt G α =>
    let some w := res.totalWitness?
      | match diagnoseTotality res with
        | .filters =>
          throwError "generator_search: this generator filters — a `PGen.assume` survived \
            optimization — so it cannot be emitted at{indentExpr (mkApp G α)}, which is `Fail`-free \
            by construction.\n\nDeclare it as `G (Option _)` instead, so the type reflects that it \
            can fail."
        | .gap err? gaps =>
          throwError "generator_search: could not reconstruct a totality witness, so this \
            generator cannot be emitted at{indentExpr (mkApp G α)}.\n\n{gapMessage err? gaps}"
    let tgen ← mkAppOptM ``Subtype.val #[none, none, w]
    extractWitness (← mkAppOptM ``Palamedes.TGen.run #[some α, some tgen, some G, none])
  | .basaltOption G α =>
    if res.totalWitness?.isSome then
      report m!"this generator never fails, so the `Option` is not needed — `{← ppExpr (mkApp G α)}` will do."
    -- `totalize` accepts any generator, so this shape cannot tell a genuine filter from a
    -- reconstruction gap on its own — which is precisely how an `Option` added on a bad diagnosis
    -- would stay forever. Say so, since the check above is silent in exactly this case.
    if res.totalWitness?.isNone then
      if let .gap err? gaps := diagnoseTotality res then
        report m!"the `Option` in this generator's type may be unnecessary: nothing here \
          established that the generator can actually fail, and `totalize` accepts it either \
          way. If the gap below is fixed and the generator turns out to be total, declare it at \
          `{← ppExpr (mkApp G α)}` instead.\n\n{gapMessage err? gaps}"
    mkAppOptM ``Palamedes.PGen.totalize #[some α, some res.gen, some G, none]

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
    -- The pipeline, spelled out as the tactics a reader could run by hand. The tail differs per
    -- declared shape, because `packageFor` emits a different term for each: the carrier directly,
    -- the `TGen` witness projected, or `totalize`. A single template would be type-incorrect for
    -- two of the three. What this does *not* show is `extractWitness`'s `totality_witness` normalization,
    -- which only makes the projected term readable — the pasted version is defeq, just denser.
    let common := s!"-- generator_search ({← ppExpr mpred})
  let cg : CorrectGen ({← ppExpr mpred}) := by
    cgenerator_search
  let g : Palamedes.PGen ({← ppExpr α}) := by
    optimize_gen cg.val"
    let tail ← match target with
      | .palamedes _ => pure "
  let _ : Palamedes.PGen.total g := by
    totality
  exact g"
      | .basalt _ _ => pure "
  let w : Palamedes.PGen.total g := by
    totality
  exact w.val.run"
      | .basaltOption _ _ => pure "
  exact Palamedes.PGen.totalize g"
    TryThis.addSuggestion stx (common ++ tail)

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
  let declName? ← Term.getDeclName?
  let θ? ← declTuningBinder?
  let res ← runSynthesisPipeline α mpred true verbose θ? (declName?.getD `_gen)
  let emitted ← packageFor target res (fun msg => logWarning msg)

  -- `genFoo.sites`, the table a `SchedulePolicy` is materialized against. Emitted by the *tactic*,
  -- while `genFoo` itself is still being elaborated, because the table is closed data that does not
  -- mention the generator — only theorems *about* the constant have to wait for `@[correct]`.
  if let some declName := declName? then
    unless res.sites.isEmpty do
      let sitesVal ← Palamedes.mkSitesValue res.sites
      addAndCompile <| .defnDecl {
        name := declName ++ `sites, levelParams := [],
        type := ← mkAppM ``Array #[mkConst ``Site], value := sitesVal,
        hints := .abbrev, safety := .safe }

  -- Leave the proofs where `@[correct]` can find them. Unconditional: the tactic cannot know
  -- whether the declaration is tagged (attributes run later), and stashing an untagged declaration
  -- costs one `NameMap` entry in a non-persistent extension.
  stashSynthesis target mpred res

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
def genEq2' : Palamedes.PGen Nat := by generator_search (· = 2)          -- synthesis-internal carrier
```

Whether a generator can fail is a fact about its type, visible at every use site:

| totality | declared | result |
|---|---|---|
| succeeds | `G α` | emitted from the `TGen` witness |
| fails | `G (Option α)` | emitted via `totalize` |
| fails | `G α` | **error** — declare `G (Option α)` |
| succeeds | `G (Option α)` | warning — it never fails, `G α` will do |

Row 3 is an *error* rather than the warning it is for a `Palamedes.PGen α` goal, and that asymmetry is
forced: `G α` is `Fail`-free by construction, so there is simply no term to emit. For the internal
`Palamedes.PGen α` carrier there is one — it just filters — so that case warns and proceeds.

A generator with no `Tuning` binder ships uniform, which diverges for a static- or growing-seed
generator like `genWellTyped`. To weight it, give the declaration a `(θ : Tuning := .uniform)`
binder: every choice site is then threaded with `θ`, `<gen>.sites` is emitted alongside, and
`<gen> … (SchedulePolicy.stlc.materialize <gen>.sites)` is the weighted generator. Support is
unaffected by the weighting, for every `θ`.

-/
syntax (name := generatorSearch) "generator_search " term : tactic

@[tactic generatorSearch]
def expandGeneratorSearch : Tactic := fun stx => do
  match stx with
  | `(tactic| generator_search $t) => generatorSearchElab stx t false
  | _ => throwError "invalid syntax"

/-- `generator_search?` is `generator_search` (same modifiers, same result) that additionally emits
the synthesized generator as a "Try this" suggestion, so the term can be pasted in place of the
tactic call. Useful for inspecting what the search actually produced, and the escape hatch into
editing it by hand.

Kept as its own `syntax` declaration rather than folded into an optional `"?"?` token on
`generator_search`. That collapse costs five lines of duplication and breaks the spelling: with
`"generator_search" "?"?`, `generator_search? P` does not lex (only `generator_search ? P` does),
because `generator_search?` is then not a token. Lean core keeps `simp`/`simp?` and `rw`/`rw?`
separate for the same reason. -/
syntax (name := generatorSearch?) "generator_search? " term : tactic

@[tactic generatorSearch?]
def expandGeneratorSearch? : Tactic := fun stx => do
  match stx with
  | `(tactic| generator_search? $t) => generatorSearchElab stx t true
  | _ => throwError "invalid syntax"
