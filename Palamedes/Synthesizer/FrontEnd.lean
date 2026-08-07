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
# The `generator_search` Front-End

The user-facing pipeline:
- search (`cgenerator_search`);
- extract a raw `PGen`;
- optimize;
- build a totality witness;
- package at the declared shape: `G α` from the `TGen` witness, or `G (Option α)` by reading the
  carrier at `OptionT G`.

**Both declarable shapes are Basalt's.** `Palamedes.PGen` is the pipeline's internal carrier and
nothing more; `classifyGoal` rejects a goal typed at it along with every other type that is not a
Basalt generator monad. So a generator declared total whose totality cannot be reconstructed is an
*error* — `G α` is `Fail`-free by construction, leaving no term to emit — rather than a warning,
which `lake build` would exit 0 on.

`runSynthesisPipeline` is the shared core; the `@[correct]` attribute (`Correct.lean`) reads the
proofs it leaves behind.
-/

open Lean Tactic Elab Meta Tactic

initialize
  registerTraceClass `palamedes.trace

register_option palamedes.debug : Bool := {
  defValue := false
  descr := "enable debug messages from palamedes"
}

/-- Pull the raw `PGen` out of a synthesized `CorrectGen` term by rewriting with the `extract` simp
set, which holds one `.val` equation per synthesis combinator. Unlike delta-reduction via
`withReducible (reduce ·)`, this unfolds exactly the combinator wrappers and nothing else, so the
combinators don't need to be `@[reducible]`.

Returns the extracted generator and the proof `e = extracted`. -/
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

/-- Run `tactic` against a fresh goal of type `goalType` and return the resulting term. -/
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

/-- The head constants a totality goal is stuck on: those with no `@[total]` rule. -/
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
  tuningSites : Array Palamedes.TuningSiteInfo := #[]

/-- Run the synthesis pipeline against a predicate `pred : α → Prop`.

Totality is always reconstructed: both declarable shapes are Basalt's, and which one a declaration
may use is exactly the question the witness answers. -/
def runSynthesisPipeline (α pred : Expr) (verbose : Bool)
    (tuningBinder : Option Expr := none) (declName : Name := `_gen) :
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

  -- 3a. Tuning: thread the declaration's `Tuning` binder through every choice site.
  let (gen''', tuneProof?, tuningSites) ←
    match tuningBinder with
    | none => pure (gen'', none, #[])
    | some θ =>
      try
        let r ← Palamedes.installTuning declName θ gen''
        if verbose then
          logInfo m!"Tuned generator ({r.sites.size} sites):\n{(← ppExpr r.gen)}"
        pure (r.gen, r.supportProof?, r.sites)
      catch e =>
        throwError m!"Failed while installing tuning.\n{e.toMessageData}"

  -- 3b. Rebuild the support proof.
  let supportProof ← do
    let supportFn := mkApp (Expr.const ``Palamedes.PGen.support []) α
    let viaExtract ← mkEqSymm (← mkCongrArg supportFn extractProof)
    let chained ← mkEqTrans (← mkEqSymm optProof) (← mkEqTrans viaExtract cgenProp)
    let chained ← match tuneProof? with
      | none => pure chained
      | some p => mkEqTrans (← mkEqSymm p) chained
    let stmt ← mkEq (← mkAppM ``Palamedes.PGen.support #[gen''']) pred
    unless ← isDefEq (← inferType chained) stmt do
      throwError "generator_search: the composed support proof does not match{indentExpr stmt}\n\
        proof has type{indentExpr (← inferType chained)}"
    mkExpectedTypeHint chained stmt

  -- 4. Totality: rebuild a `TGen` witness over the combinator spine.
  let mut totalWitness? : Option Expr := none
  let mut totalityFailure? : Option MessageData := none
  let mut gaps : Array Name := #[]
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
           tuningSites }

/-- What the declared return type says the generator should be. Whether a generator filters is a
fact about its type, visible at every use site. -/
inductive Target where
  /-- `G α` for a Basalt `[Gen G]`. Emitted from the `TGen` witness, so it is `Fail`-free. -/
  | basalt (G α : Expr)
  /-- `G (Option α)` for a Basalt `[Gen G]`. Emitted by reading the carrier at `OptionT G`, where a
  failed guard is a `none`. -/
  | basaltOption (G α : Expr)

/-- The element type the predicate must range over. -/
def Target.elemType : Target → Expr
  | .basalt _ α | .basaltOption _ α => α

/-! ## The synthesis stash

`generator_search` proves `support gen = P` and then closes a goal; the theorem it could state about
the declaration cannot be added yet, because during the tactic that declaration does not exist. The
`@[correct]` attribute (`Synthesizer/Correct.lean`) runs *after* it does, so the tactic leaves the
proof here and the attribute picks it up.
-/

/-- `Target` with the `Expr`s dropped. The stash outlives the elaboration its `Expr`s were built in,
and the shape is all the attribute needs: it chooses which law is stated. -/
inductive Shape where
  | basalt | basaltOption
  deriving Inhabited, BEq

def Target.shape : Target → Shape
  | .basalt _ _ => .basalt
  | .basaltOption _ _ => .basaltOption

/-- What `generator_search` leaves for `@[correct]`.

Every field is **closed over the declaration's binder telescope** (`fun xs => …`) and
**metavariable-free**. Both are load-bearing: the attribute runs in a fresh `MetaM` where neither
the tactic's local context nor its metavariable context exists, so an open term's `fvar`s are
dangling and a surviving mvar surfaces there as `unknown universe metavariable ?_uniq.N` reported
against the `def` — with no `?m` visible anywhere in it. `stashSynthesis` therefore checks rather
than assumes. -/
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
  /-- `fun xs => (h : emitted = PGen.totalize gen)`, at the filtering shape.

  The emitted term is the carrier read at `OptionT G` with the projection pushed inward, which is
  the *same generator* but not definitionally the same term — pushing past a `dite` or a `match` is
  a case analysis on a stuck scrutinee. The law is stated about `totalize`, so this is what carries
  it across. `none` at the total shape, which needs no such step. -/
  partialEq? : Option Expr

initialize synthesisExt : EnvExtension (NameMap SynthesisStash) ←
  registerEnvExtension (pure {})

/-- The binders of the declaration currently being elaborated, as they stand at the tactic's site.

The recursive self-reference is in scope too (`genFoo : ℕ → ℕ → PGen α`), flagged `isAuxDecl`.
Dropping it and any implementation detail leaves exactly the telescope that `forallTelescope
ci.type` yields once the constant exists, in the same order — including auto-bound implicits. That
positional correspondence is what lets the attribute re-open a stashed `fun xs => _` with `.beta`.
-/
def declBinders : MetaM (Array Expr) := do
  let mut xs := #[]
  for d? in (← getLCtx).decls do
    if let some d := d? then
      unless d.isAuxDecl || d.isImplementationDetail do
        xs := xs.push d.toExpr
  return xs

/-- The declaration's `Tuning` binder, if it declared one. -/
def declTuningBinder? : MetaM (Option Expr) := do
  for x in ← declBinders do
    if (← whnf (← inferType x)).isConstOf ``Tuning then return some x
  return none

/-- Record a completed synthesis for `@[correct]`, if we are elaborating into a named declaration.
-/
def stashSynthesis (target : Target) (pred : Expr) (res : SynthesisResult)
    (partialEq? : Option Expr) : TermElabM Unit := do
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
    totalWitness? := ← res.totalWitness?.mapM close
    partialEq? := ← partialEq?.mapM close }
  modifyEnv (synthesisExt.modifyState · (·.insert declName stash))

/-- Elaborate `t` as a predicate `α → Prop`, returning `none` if it does not fit that type. -/
private def elabPredAt? (t : Lean.Term) (α : Expr) : TermElabM (Option Expr) :=
  try
    Term.withoutErrToSorry do
      let e ← Term.elabTerm t (some (.forallE `a α (.sort 0) .default))
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      if e.hasSorry || e.hasExprMVar then return none
      return some e
  catch _ => return none

/-- Read the target off the goal type, and the predicate against it. -/
def classifyGoal (goalTy : Expr) (t : Lean.Term) : TermElabM (Target × Expr) := do
  match goalTy with
  | .app G τ =>
    -- Basalt's `Gen` is universe-polymorphic, so an auto-bound `[Gen G]` binder elaborates `G` at
    -- `Type → Type ?u`. Palamedes' own generators quantify over `G : Type → Type` exactly, so pin
    -- the universe here, while `?u` is still unassigned — otherwise it only surfaces later as a
    -- mismatch inside the emitted `totalize`/`TGen.run` application, which reads as a bug in
    -- emission rather than a fact about the declared binder.
    let typeType ← mkArrow (mkSort Level.one) (mkSort Level.one)
    unless ← isDefEq (← inferType G) typeType do
      throwError "generator_search: the goal's type constructor{indentExpr G}\n\
        must have type `Type → Type`, but has{indentExpr (← inferType G)}"
    let some _ ← synthInstance? (← mkAppM ``Gen #[G])
      | throwError "generator_search: the goal's type constructor{indentExpr G}\n\
          is not a Basalt generator monad (no `Gen` instance)"
    match τ with
    | .app (.const ``Option [_]) β =>
      -- Filtering reading first (see the docstring). Elaboration is too permissive to decide the
      -- other way round: `fun n => lo ≤ n ∧ n ≤ hi` typechecks at `Option Nat → Prop` too, because
      -- Mathlib gives `Option` an `LE` instance and silently coerces `lo` to `some lo`.
      if let some p ← elabPredAt? t β then
        return (.basaltOption G β, p)
      let some p ← elabPredAt? t τ
        | throwError "generator_search: the predicate fits neither{indentExpr β} → Prop\n\
            (a filtering generator) nor{indentExpr τ} → Prop (a total generator of options)"
      return (.basalt G τ, p)
    | _ =>
      let some p ← elabPredAt? t τ
        | throwError "generator_search: the predicate must have type{indentExpr τ} → Prop"
      return (.basalt G τ, p)
  | _ =>
    throwError "generator_search: the goal must be `G α` or `G (Option α)` for a Basalt \
      `[Gen G]`, got{indentExpr goalTy}"

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

/-- Turn a totality witness back into generator code using lemmas in the `totality_witness` simp
set. -/
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

/-- Push `PGen.run` through a `match`: rebuild the matcher at the run-type motive with each arm
projected, and prove the two equal by instantiating the *same* matcher a third time, at a `Prop`
motive where every arm is `rfl` — substituting an arm's own pattern for the discriminants makes both
matchers iota-reduce to that arm.

A simproc on both counts. There is no per-datatype `X.run_cases` to write instead: a matcher
auxiliary is generated per elaboration and only *defeq* to any other, while simp matches at
`reducible`, so a lemma stated about one would never fire on another's (`X.total_cases` has the same
constraint, and answers it by being `apply`d from a keyed descent). Nor can this be a
`Meta.transform`: pushing a projection into a match arm is not definitional for a stuck scrutinee,
so each step has to carry an equation for simp to compose up through the surrounding term.

Both rebuilds retarget `uElimPos?`, the matcher's motive universe: the arms were elaborated at
`PGen α : Type 1` and are being re-elaborated at `G (Option α) : Type` and at `Prop`. Reusing the
levels unchanged is what makes the kernel reject the result with a motive arity mismatch. -/
private def pushRunMatch : Simp.Simproc := fun e => do
  let_expr Palamedes.PGen.run α scrut G gi fi := e | return .continue
  let some m ← matchMatcherApp? scrut | return .continue
  let some uPos := m.uElimPos? | return .continue
  let runOf (g : Expr) : Expr := mkAppN (mkConst ``Palamedes.PGen.run) #[α, g, G, gi, fi]
  let resTy := mkApp G α
  let atLevel (l : Level) := (m.matcherLevels.set! uPos l).toList
  let matcherAt (l : Level) (motive : Expr) (alts : Array Expr) :=
    mkAppN (mkConst m.matcherName (atLevel l)) (m.params ++ #[motive] ++ m.discrs ++ alts)
  let motive' ← lambdaTelescope m.motive fun xs _ => mkLambdaFVars xs resTy
  let alts' ← m.alts.mapIdxM fun i alt =>
    lambdaBoundedTelescope alt m.altNumParams[i]! fun xs body => mkLambdaFVars xs (runOf body)
  let lvl ← getLevel resTy
  let expr := matcherAt lvl motive' alts'
  let eqMotive ← lambdaTelescope m.motive fun xs _ => do
    let orig := mkAppN (mkConst m.matcherName m.matcherLevels.toList)
      (m.params ++ #[m.motive] ++ xs ++ m.alts)
    let pushed := mkAppN (mkConst m.matcherName (atLevel lvl))
      (m.params ++ #[motive'] ++ xs ++ alts')
    mkLambdaFVars xs (← mkEq (runOf orig) pushed)
  let eqAlts ← m.alts.mapIdxM fun i alt =>
    lambdaBoundedTelescope alt m.altNumParams[i]! fun xs body => do
      mkLambdaFVars xs (← mkEqRefl (runOf body))
  let proof := matcherAt Level.zero eqMotive eqAlts
  -- A motive rebuilt at the wrong universe, or an arm whose `rfl` does not in fact hold, produces a
  -- term the kernel rejects much later and far from here.
  unless ← isDefEq (← inferType proof) (← mkEq e expr) do return .continue
  return .visit { expr, proof? := some proof }

/-- Read a generator that kept an `assume` at `OptionT G`, where `Fail` is `pure none`, and push the
projection down until what is left is Basalt vocabulary.

`PGen.totalize g` denotes exactly this in a single constant, but it leaves the carrier wrapped
around the generator, which would make the filtering shape the one shape whose emitted term is not
readable as Basalt code.

Three things do not push on their own. `dite`/`ite` get `PGen.run_dite`/`run_ite`; a `match` gets
`pushRunMatch`; and a datatype's primitive gets unfolded to its `TGen` spelling, whose head
constants are read off the `@[total]` registry — each rule is keyed by the `PGen` head it
reconstructs, which is exactly the set to unfold. `dite`/`ite` are registered heads too and are
excluded: delta-unfolding them exposes `Decidable.rec`, which is not a case split any more.

Recursion needs nothing: `X.run_unfold` is stated at an arbitrary `G` with `Fail G`, so it fires at
`OptionT G` like anywhere else, and `X.unfoldGo`'s own polymorphism does the short-circuiting.

Returns the term and a proof that it equals `PGen.totalize gen`, which the filtering law is stated
against. The equation is not `rfl`: `run_dite` and the match push are both case analyses on a stuck
scrutinee. -/
def extractPartialWitness (α gen G : Expr) : MetaM (Expr × Expr) := do
  let optT ← mkAppM ``OptionT #[G]
  let e ← mkAppOptM ``Palamedes.PGen.run
    #[α, gen, optT, ← synthInstance (← mkAppM ``Gen #[optT]),
      ← synthInstance (← mkAppM ``Palamedes.Fail #[optT])]
  let prims := (Palamedes.totalRules (← getEnv)).map (·.head)
    |>.filter (fun n => n != ``dite && n != ``ite)
  let some pwExt ← getSimpExtension? `partial_witness
    | throwError "simp extension `partial_witness` not found"
  let mut thms ← pwExt.getTheorems
  for n in Palamedes.pgenBasis ++ prims do
    thms ← thms.addDeclToUnfold n
  -- `List.map_cons`/`_nil` so a choice's branch list actually computes: without them `.run` stays
  -- stuck under the `List.map` lambda `frequency`'s branches are built by, and every branch is left
  -- as a bare `PGen.mk`.
  for n in [``Palamedes.PGen.run_dite, ``Palamedes.PGen.run_ite, ``Palamedes.run_fail,
            ``List.map_cons, ``List.map_nil] do
    thms ← thms.addConst n
  -- `proj := true` cancels the `PGen.mk`/`.run` pair and computes the `Prod` projections a choice's
  -- branch list is built from. It also reduces `Pure.pure`/`Bind.bind` through the
  -- `Gen (OptionT G)` instance, so the result names `OptionT.pure`/`OptionT.bind` — the honest
  -- reading, since the term *is* at `OptionT G`.
  let ctx ← Simp.mkContext
    (config := { proj := true, zetaDelta := true })
    (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  -- The simproc's index key. Built from metavariables rather than `mkAppOptM`, which would try to
  -- *synthesize* the `Gen`/`Fail` instances of a `G` that is only a pattern here.
  let key ← withReducible do
    let β ← mkFreshExprMVar (mkSort 1)
    let g ← mkFreshExprMVar (mkApp (mkConst ``Palamedes.PGen) β)
    let Gp ← mkFreshExprMVar (← mkArrow (mkSort 1) (mkSort 1))
    let gi ← mkFreshExprMVar (← mkAppM ``Gen #[Gp])
    let fi ← mkFreshExprMVar (← mkAppM ``Palamedes.Fail #[Gp])
    DiscrTree.mkPath (mkAppN (mkConst ``Palamedes.PGen.run) #[β, g, Gp, gi, fi])
  let sprocs : Simp.Simprocs :=
    ({} : Simp.Simprocs).addCore key `pushRunMatch true (.inl pushRunMatch)
  let (r, _) ← simp e ctx #[sprocs]
  let proof ← match r.proof? with
    | some p => mkEqSymm p
    | none => mkEqRefl e
  let expr ← dropIdentityTransports r.expr
  -- `dropIdentityTransports` rewrites proof subterms only, so the equation still holds of the
  -- result; retype it rather than rebuilding it.
  let totalized ← mkAppOptM ``Palamedes.PGen.totalize #[some α, some gen, some G, none]
  return (expr, ← mkExpectedTypeHint proof (← mkEq expr totalized))

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
    filters. Declaring it at `G (Option _)` would compile — that shape accepts any generator — but \
    it would bury the gap behind an `Option` the generator does not need, and weaken the emitted \
    law from `IsSoundAndComplete` to `IsSomeSoundAndComplete`. Fix the registration instead."

/-- Package the pipeline's result at the shape the declaration asked for.

This is the whole of "Basalt owns the vocabulary": the pipeline is identical in every case and only
the final packaging differs.

The second component is the filtering shape's `emitted = PGen.totalize gen` equation, which
`@[correct]` needs to state its law against the constant. `none` at the total shape, whose emitted
term is defeq to what its law is about. -/
def packageFor (target : Target) (res : SynthesisResult) (report : MessageData → TermElabM Unit) :
    TermElabM (Expr × Option Expr) := do
  match target with
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
    return (← extractWitness (← mkAppOptM ``Palamedes.TGen.run #[some α, some tgen, some G, none]),
            none)
  | .basaltOption G α =>
    match res.totalWitness? with
    | some _ =>
      report m!"this generator never fails, so the `Option` is not needed — `{← ppExpr (mkApp G α)}` will do."
    | none =>
      -- Reading a generator at `OptionT` works whether or not it can fail, so this shape cannot
      -- tell a genuine filter from a reconstruction gap on its own — which is precisely how an
      -- `Option` added on a bad diagnosis would stay forever. Say so, since the "never fails" check
      -- above is silent in exactly this case.
      if let .gap err? gaps := diagnoseTotality res then
        report m!"the `Option` in this generator's type may be unnecessary: nothing here \
          established that the generator can actually fail, and reading it at `OptionT` accepts it \
          either way. If the gap below is fixed and the generator turns out to be total, declare \
          it at `{← ppExpr (mkApp G α)}` instead.\n\n{gapMessage err? gaps}"
    let (e, h) ← extractPartialWitness α res.gen G
    return (e, some h)

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
    -- declared shape, because `packageFor` emits a different term for each, and a single template
    -- would be type-incorrect for one of the two. What this does *not* show is the normalization
    -- that follows — `extractWitness` on the total side, the `.run` push on the filtering one. Both
    -- only make the term readable, so the tails below close the same goals, just densely.
    let common := s!"-- generator_search ({← ppExpr mpred})
  let cg : CorrectGen ({← ppExpr mpred}) := by
    cgenerator_search
  let g : Palamedes.PGen ({← ppExpr α}) := by
    optimize_gen cg.val"
    let tail ← match target with
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

  let declName? ← Term.getDeclName?
  let θ? ← declTuningBinder?
  let res ← runSynthesisPipeline α mpred verbose θ? (declName?.getD `_gen)
  let (emitted, partialEq?) ← packageFor target res (fun msg => logWarning msg)

  -- `genFoo.sites`, the table a `SchedulePolicy` is materialized against. Emitted by the *tactic*,
  -- while `genFoo` itself is still being elaborated, because the table is closed data that does not
  -- mention the generator — only theorems *about* the constant have to wait for `@[correct]`.
  if let some declName := declName? then
    unless res.tuningSites.isEmpty do
      let sitesVal ← Palamedes.mkSitesValue res.tuningSites
      addAndCompile <| .defnDecl {
        name := declName ++ `sites, levelParams := [],
        type := ← mkAppM ``Array #[mkConst ``Site], value := sitesVal,
        hints := .abbrev, safety := .safe }

  -- Leave the proofs where `@[correct]` can find them. Unconditional: the tactic cannot know
  -- whether the declaration is tagged (attributes run later), and stashing an untagged declaration
  -- costs one `NameMap` entry in a non-persistent extension.
  stashSynthesis target mpred res partialEq?

  if tryThis then
    withOptions ((pp.proofs.set · true) ∘ (pp.fieldNotation.generalized.set · false)) do
      TryThis.addExactSuggestion stx emitted

  closeMainGoal `generator_search emitted

/-- `generator_search P` closes a generator goal with a generator whose support is exactly `P` —
it can produce every value satisfying `P`, and nothing else. `P` may be a `Prop`-valued predicate or
a decidable `α → Bool`, including a recursive one over a `derive_palamedes`d datatype.

We use the declared return type to determine the failure behavior; a return type of `G α` defaults
to a generator that may not backtrack, whereas one declared at type `G (Option α)` is allowed to
backtrack if necessary:

```lean
def genEq2 [Gen G] : G Nat := by generator_search (· = 2)               -- total
def genRBT [Gen G] : G (Option (Tree Nat)) := by generator_search isRBT -- filtering
```

Palamedes can also automatically add tuning parameters, which can be used for manual or automated
tuning. Simply add a parameter of type `Tuning`:

```lean
def genRBT [Gen G] (lo hi : Nat) (θ : Tuning) : G (Tree Nat) := by
  generator_search (fun t => isBST lo hi t)
```
-/
syntax (name := generatorSearch) "generator_search " term : tactic

@[tactic generatorSearch]
def expandGeneratorSearch : Tactic := fun stx => do
  match stx with
  | `(tactic| generator_search $t) => generatorSearchElab stx t false
  | _ => throwError "invalid syntax"

/-- `generator_search?` is `generator_search` that additionally emits the synthesized generator as a
"Try this" suggestion, so the term can be pasted in place of the tactic call. Useful for inspecting
what the search actually produced, and the escape hatch into editing it by hand. -/
syntax (name := generatorSearch?) "generator_search? " term : tactic

@[tactic generatorSearch?]
def expandGeneratorSearch? : Tactic := fun stx => do
  match stx with
  | `(tactic| generator_search? $t) => generatorSearchElab stx t true
  | _ => throwError "invalid syntax"
