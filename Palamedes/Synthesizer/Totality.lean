import Palamedes.Data.List
import Palamedes.Data.Stack.Stack
import Palamedes.Data.STLC.Ty
import Palamedes.Data.STLC.Term
import Palamedes.Data.Tree
import Palamedes.Data.Nat
import Palamedes.Total

open Palamedes Palamedes.Gen Palamedes.Gen.Total

/-- Case-split the discriminant of a `match` sitting inside a totality goal.

`split` would also close these goals, but it emits a `splitter` application carrying an `Eq.rec` cast
per arm — and since `total` is `Type`-valued, that cast lands in the **data** path of the witness. It
blocks `.val` from projecting, so the emitted generator cannot be reduced back to generator code and
lands in the environment as a proof term. Casing the discriminant directly lets the `match`
iota-reduce, so no cast is ever created. `PalamedesTest/Extract.lean` audits for the difference. -/
elab "total_cases" : tactic => open Lean Elab Tactic Meta in do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  unless ty.isAppOf ``Palamedes.Gen.total do
    throwError "total_cases: goal is not `Gen.total _`"
  let some app ← matchMatcherApp? ty.appArg!
    | throwError "total_cases: the generator is not a `match` application"
  for d in app.discrs do
    if let .fvar fv := d then
      let subgoals ← goal.cases fv
      replaceMainGoal (subgoals.map (·.mvarId)).toList
      return
  throwError "total_cases: no discriminant is a local hypothesis to case on"

/-- Prove `Gen.total g` by reconstructing a `TGen` (`Fail`-free) witness over `g`'s combinator spine.

Each `total_*` lemma maps one `Gen` combinator to its `TGen` twin and closes by `ext; rfl`, so the
`apply` cascade is the structural reconstruction. `optimizeGen` has already eliminated every
satisfiable `assume`, so an `assume` reaching this tactic denotes a genuine filter and reconstruction
fails (the generator is partial; declare it at `G (Option α)`, which is what makes
`generator_search` emit it via `totalize` instead).

Two things about the cascade below are not obvious:

* **The combinator basis is ordered.** `total_oneOf` must precede `total_frequency`: `oneOf` is
  definitionally a `frequency`, so the latter would capture the goal and leave a stuck
  `totalWeighted (List.map …)`. That is why the basis is hard-coded here rather than registered.
* **The per-datatype rules are not**, so they come from the `@[total]` registry, and a new datatype
  needs no edit to this file. Their goal shapes are pairwise disjoint, so at most one can ever apply.

`total_cases`/`simp` at the end handle recursion: an `unfold` step is wrapped in a constructor
`match`, and `(casesOn a …).toGen = casesOn a (…toGen)` is not definitional — it needs `cases a`. -/
elab "totality" : tactic => open Lean Elab Tactic in do
  let leaves ← (Palamedes.totalLemmas (← getEnv)).mapM fun n =>
    `(tactic| apply $(mkIdent (`_root_ ++ n)):term)
  evalTactic (← `(tactic|
    repeat'
      first
        | (intro)
        | apply total_pure
        | apply total_bind
        | apply total_pick
        | apply total_oneOf
        | apply total_frequency
        | apply totalList_cons
        | apply totalList_nil
        | apply totalWeighted_cons
        | apply totalWeighted_nil
        | apply total_map
        | apply total_dite
        $[| $leaves:tactic]*
        | total_cases
        -- `split` stays as a last resort. It leaves a cast in the witness, so a datatype that falls
        -- through to it fails the extraction audit rather than silently emitting a proof term.
        | split
        | simp (config := {singlePass := true})))
