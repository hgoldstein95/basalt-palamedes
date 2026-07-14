import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Optimizer
import Palamedes.Synthesizer.CGeneratorSearch
import Palamedes.Synthesizer.Totality

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
-/
def extractGen (e : Expr) : MetaM Expr := do
  let some ext ← getSimpExtension? `extract
    | throwError "simp extension `extract` not found"
  let ctx ← Simp.mkContext
    (config := { zetaDelta := true })
    (simpTheorems := #[← ext.getTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let (result, _) ← simp e ctx
  return result.expr

/-- This is just a utility tactic for debugging. We don't call it in the real synthesizer. -/
elab "optimize_gen " t:term : tactic =>
  withMainContext do
    let m ← mkFreshExprMVar (some (.sort 0))
    let gen ← elabTerm t (some (.app (.const ``Palamedes.Gen []) m))
    let gen' ← extractGen gen
    let (gen'', _) ← Palamedes.optimizeGen gen'
    let gen''' ← withReducible (reduce gen'')
    closeMainGoal `optimize_gen gen'''

def solveGoalWithTactic (goalType : Expr) (tactic : TSyntax `tactic) : TacticM Expr := do
  let m ← mkFreshExprMVar goalType
  let unsolved ← evalTacticAt tactic m.mvarId!
  if unsolved.length > 0 then do
    throwError "goals left unsolved: {unsolved}"
  instantiateMVars m

def generatorSearchElab
    (stx : Syntax)
    (t : Lean.Term)
    (checkTotal : Bool)
    (tryThis : Bool)
    (schedules : Bool := false) :
    TacticM Unit := do
  let opts ← getOptions
  let verbose := palamedes.debug.get opts

  let g ← getMainGoal
  let .app (.const ``Palamedes.Gen []) α ← g.getType
    | throwError "goal type must be Gen α for some α"
  let ty := .forallE `α α (.sort 0) .default
  let mpred ← elabTerm t (some ty)

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

  -- Synthesize a correct generator by solving `CorrectGen P` and projecting the `.val`.
  let gen ← do
    try
      let cgen ← solveGoalWithTactic
        (mkAppN (.const ``Palamedes.CorrectGen []) #[α, mpred])
        (← `(tactic| cgenerator_search))
      extractGen (← mkAppM ``Subtype.val #[cgen])
    catch e =>
      throwError m!"Failed during generator synthesis.\n{e.toMessageData}"
  if verbose then do
    logInfo m!"Synthesized generator:\n{(← ppExpr gen)}"
  let gen' ←
    try
      let (gen', proof) ←
        Palamedes.optimizeGen gen (if schedules then some Palamedes.decayPolicy else none)
      Lean.Meta.check proof
      withReducible (reduce gen')
    catch e =>
      throwError m!"Failed during optimization.\n{e.toMessageData}"
  if verbose then do
    logInfo m!"Optimized generator:\n{(← ppExpr gen')}"

  -- Optionally: check that the generator is total, i.e. assume-free — it never filters. (This is
  -- *not* almost-sure termination, which is orthogonal and which nothing here establishes.)
  if checkTotal then do
    try
      let _ ← solveGoalWithTactic
        (← mkAppM ``Palamedes.Gen.total #[gen'])
        (← `(tactic| totality))
    catch e =>
      logWarning m!"Failed during totality checking.
      {e.toMessageData}
      {gen'}
      could not be proved total: a `Gen.assume` survived optimization, so this generator filters \
      and can fail when sampled.

      Use `generator_search {t} allow_partial` to accept that and turn off this check."

  if tryThis then
    withOptions ((pp.proofs.set · true) ∘ (pp.fieldNotation.generalized.set · false)) do
      TryThis.addExactSuggestion stx gen'

  closeMainGoal `generator_search gen'

/--
`generator_search P` closes a `Gen α` goal with a generator whose *support* is exactly `P` — it can
produce every value satisfying `P`, and nothing else. `P` may be a `Prop`-valued predicate or a
decidable `α → Bool`, including a recursive one over any `derive_palamedes`d datatype.

```lean
def genEq2 : Gen Nat := by generator_search (· = 2)
```

Two modifiers, in this order:

* **`allow_partial`** skips the totality check, admitting a generator that still contains a
  `Gen.assume` — i.e. one that *filters*. Such a generator can fail when sampled (the sampler does
  not backtrack), so this is opt-in. Needed by `genAVL` and `genRBT`.

* **`with_schedules`** weights each choice under a recursion by depth (`w(d) = a + b·d`) so that
  branching starts supercritical near the root and decays, which is what makes a *static- or
  growing-seed* generator terminate in practice — `genWellTyped` diverged on 54.3% of draws without
  it. Leave it off for a *shrinking-seed* generator (`genBST`, `genLengthK`, `Range`), which already
  terminates and would only lose size to the decay. Nothing infers which you have; it is your call.
  Support is unaffected either way.

Totality failure is a *warning*, not an error.
-/
syntax (name := generatorSearch) "generator_search " term " allow_partial"? " with_schedules"? :
  tactic

@[tactic generatorSearch]
def expandGeneratorSearch : Tactic := fun stx =>
  match stx with
  | `(tactic| generator_search $t allow_partial with_schedules) =>
    generatorSearchElab stx t false false (schedules := true)
  | `(tactic| generator_search $t with_schedules) =>
    generatorSearchElab stx t true false (schedules := true)
  | `(tactic| generator_search $t allow_partial) =>
    generatorSearchElab stx t false false
  | `(tactic| generator_search $t) =>
    generatorSearchElab stx t true false
  | _ => throwError "invalid syntax"

/-- `generator_search?` is `generator_search` (same modifiers, same result) that additionally emits
the synthesized generator as a "Try this" suggestion, so the term can be pasted in place of the
tactic call. Useful for inspecting what the search actually produced. -/
syntax (name := generatorSearch?) "generator_search? " term " allow_partial"? " with_schedules"? :
  tactic

@[tactic generatorSearch?]
def expandGeneratorSearch? : Tactic := fun stx =>
  match stx with
  | `(tactic| generator_search? $t allow_partial with_schedules) =>
    generatorSearchElab stx t false true (schedules := true)
  | `(tactic| generator_search? $t with_schedules) =>
    generatorSearchElab stx t true true (schedules := true)
  | `(tactic| generator_search? $t allow_partial) =>
    generatorSearchElab stx t false true
  | `(tactic| generator_search? $t) =>
    generatorSearchElab stx t true true
  | _ => throwError "invalid syntax"
