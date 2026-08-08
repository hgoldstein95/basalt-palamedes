/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Data.List
import Palamedes.Data.Stack.Stack
import Palamedes.Data.STLC.Ty
import Palamedes.Data.STLC.Term
import Palamedes.Data.Tree
import Palamedes.Data.Nat
import Palamedes.Total

/-!
# The `totality` tactic

Stage 4 of the pipeline: reconstruct a `TGen` (`Fail`-free) witness over a generator's combinator
spine, by descending it and dispatching each node on its head constant to the `@[total]` rule that
reconstructs that head.

**This file names no lemmas.** The generic combinator basis (`Palamedes/Total.lean`) and the
per-datatype leaves (`Palamedes/Data/`, plus everything `derive_palamedes` emits) are registered the
same way, so adding either needs no edit here.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.Total

/-- How many definitions deep to look for a head the registry knows. See `total_apply`. -/
private def unfoldBudget : Nat := 8

/-- Reconstruct one node: dispatch the goal's head constant to its `@[total]` rule and `apply` it.

`apply` rather than a hand-built application: the rule's structural, implicit and instance arguments
and its universe levels all have to be solved against the goal, and `apply` is Lean's solver for
exactly that. Dispatch only chooses *which* rule to hand it.

**A head with no rule is unfolded and looked up again**, because a totality goal need not be stated
about a spine: `PGen.total genAllTwos` names a generator that *contains* one. Unfolding only where
the registry has no rule is what keeps dispatch exact — a combinator in the basis is never unfolded,
so `PGen.oneOf` cannot collapse into the `PGen.frequency` it is defined as. The
reachable-but-unregistered case pays a bounded `unfoldBudget` before giving up; `PGen.assume` is
what reaches that bound in practice, and giving up there is the intended "this generator filters"
outcome. -/
elab "total_apply" : tactic => open Lean Elab Tactic Meta in do
  let goal ← getMainGoal
  goal.withContext do
    let table := Palamedes.totalTable (← getEnv)
    let mut ty ← instantiateMVars (← goal.getType)
    let mut decl? : Option Name := none
    for _ in [0:unfoldBudget] do
      let some key ← Palamedes.totalKey? ty
        | throwError "total_apply: the goal is not a totality goal about a term with a head \
            constant{indentExpr ty}"
      if let some d := table[key]? then
        decl? := some d
        break
      let some unfolded ← unfoldDefinition? ty.appArg!.headBeta
        | throwError "total_apply: no `@[total]` rule reconstructs `{key.2}`, and it does not unfold"
      let args := ty.getAppArgs
      ty := mkAppN ty.getAppFn (args.set! (args.size - 1) unfolded)
    let some decl := decl?
      | throwError "total_apply: no `@[total]` rule reconstructs the head of{indentExpr ty}\n\
          (gave up after unfolding {unfoldBudget} definitions deep)"
    -- Against the *original* goal, not the unfolded one: `apply` unifies up to delta anyway, so
    -- unfolding is a way to find the rule, not a change to what is being proved.
    replaceMainGoal (← goal.apply (← mkConstWithFreshMVarLevels decl))

/-- Case-split the discriminant of a `match` sitting inside a totality goal.

The fallback for a `match` whose base functor has no `X.total_cases` — `derive_palamedes` emits one
per datatype, so in practice this is reached only by a hand-written match.

`split` would also close these goals, but it emits a `splitter` application carrying an `Eq.rec` cast
per arm — and since `total` is `Type`-valued, that cast lands in the **data** path of the witness. It
blocks `.val` from projecting, so the emitted generator cannot be reduced back to generator code and
lands in the environment as a proof term. Casing the discriminant directly lets the `match`
iota-reduce, so no cast is ever created. `PalamedesTest/Extract.lean` audits for the difference. -/
elab "total_cases" : tactic => open Lean Elab Tactic Meta in do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  unless ty.isAppOf ``Palamedes.PGen.total do
    throwError "total_cases: goal is not `PGen.total _`"
  let some app ← matchMatcherApp? ty.appArg!
    | throwError "total_cases: the generator is not a `match` application"
  for d in app.discrs do
    if let .fvar fv := d then
      let subgoals ← goal.cases fv
      replaceMainGoal (subgoals.map (·.mvarId)).toList
      return
  throwError "total_cases: no discriminant is a local hypothesis to case on"

/-- Prove `PGen.total g` by reconstructing a `TGen` (`Fail`-free) witness over `g`'s combinator spine.

Each `@[total]` rule maps one `PGen` head to its `TGen` twin, so descending the spine and dispatching
on the head *is* the structural reconstruction. `optimizeGen` has already eliminated every
satisfiable `assume`, so an `assume` reaching this tactic denotes a genuine filter: nothing
reconstructs `PGen.assume`, the dispatch finds no rule, and the goal is left open (which is what
makes `generator_search` emit the generator via `totalize` instead).

Dispatch is a lookup on the goal's head, not a search, and that is what keeps the four arms below
from interacting:

* `total_apply` is a *function* of the goal. Two rules can never race for one node, since `@[total]`
  rejects a second rule claiming a head already claimed, so this file has no ordering to get right.
* `total_cases` fires only where dispatch found nothing *and* the node is a `match`, and `split`
  only where even that did not apply. Both leave a cast in the witness, so a datatype reaching them
  fails the extraction audit rather than silently emitting a proof term.
* `simp` last, single-pass so it cannot loop on the recursive `unfold` equations.

`repeat'` never fails, so a goal none of the four can step is simply left open — see
`diagnoseNoWitness`, which is what tells a genuine filter apart from a missing registration. -/
elab "totality" : tactic => open Lean Elab Tactic in do
  evalTactic (← `(tactic|
    repeat'
      first
        -- Parenthesized: bare `intro` accepts match-style patterns, so it swallows the next `|` and
        -- the quotation fails to parse with "expected '=>'".
        | (intro)
        | total_apply
        | total_cases
        | split
        | simp (config := {singlePass := true})))
