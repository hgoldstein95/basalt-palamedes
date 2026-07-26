/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Data
import Palamedes.Synthesizer.FrontEnd

/-!
# `totality` dispatch regressions

Two things, both of which fail two modules away if they drift.

`total_apply` dispatches each node on its head constant, so what is registered *is* what is
reachable. This file pins that the registry has no shadowed rule and that `@[total]` rejects one.

`total_cases` is what keeps the totality witness in the *data* path when dispatch finds nothing: it
cases the `match` discriminant directly, so the `match` iota-reduces and no `Eq.rec` cast is
created. When it declines, `totality` falls through to `split`, which *does* close the goal — while
leaving the cast that `PalamedesTest/Extract.lean` then rejects. So a precondition silently drifting
surfaces as extraction residue rather than as a tactic error.
-/

open Palamedes Palamedes.PGen

/-! ## Every registered rule is reachable

Dispatch is keyed on the tag, so the table and the registry must agree entry for entry: a mismatch
means some rule is shadowed and silently unreachable. A rule listed nowhere but the registry is the
easy case to lose, since a `simp` fallback can mask it. -/
run_cmd do
  let rules := Palamedes.totalRules (← Lean.getEnv)
  let table := Palamedes.totalTable (← Lean.getEnv)
  unless table.size == rules.size do
    throwError "the `@[total]` registry has {rules.size} rules but dispatches to only \
      {table.size} heads, so some rule is shadowed and unreachable"
  -- ...and the basis is registered rather than named in the tactic, so it is in here too.
  for n in [``PGen.Total.total_oneOf, ``PGen.Total.total_frequency, ``PGen.Total.total_bind,
            ``PGen.Total.total_color_rec] do
    unless rules.any (·.decl == n) do
      throwError "`{n}` is not in the `@[total]` registry, so `totality` cannot dispatch to it"

-- Two rules for one head is a tag-time error, not a silent shadowing: rules that could race for a
-- goal cannot coexist in the registry at all.
/--
error: @[total]: `PalamedesTest.shadowsPure` and `Palamedes.PGen.Total.total_pure` both reconstruct `Pure.pure`, so the `totality` tactic would have to choose between them. Keep one, or give them distinct heads.
-/
#guard_msgs in
@[total] def PalamedesTest.shadowsPure (a : α) : PGen.total (Pure.pure a) :=
  PGen.Total.total_pure a

/-! ## An unreconstructible head is named, not guessed

`totality` is `repeat' first | …`, which never fails, so an unclosed goal carries no information
about *why* on its own — a diagnosis built from the goal alone can only guess at "some datatype with
no `@[total]` lemma" and leave the reader to find which. A dispatch table can be asked which head it
had no rule for, which is what keyed dispatch buys that a search over rules cannot. -/

opaque PalamedesTest.mystery : Palamedes.PGen Nat

-- The head itself is what is pinned, not `gapMessage`'s prose around it.
/-- info: [PalamedesTest.mystery] -/
#guard_msgs(info) in
run_cmd Lean.Elab.Command.liftTermElabM do
  let goal ← Lean.Meta.mkAppM ``Palamedes.PGen.total #[Lean.mkConst ``PalamedesTest.mystery]
  match ← solveGoalWithTactic? goal (← `(tactic| totality)) with
  | .ok _ => throwError "expected `totality` to leave a goal on a head with no rule"
  | .error gs => Lean.logInfo m!"{← totalityGaps gs}"

/-! ## `total_cases` preconditions -/

/-- error: total_cases: goal is not `PGen.total _` -/
#guard_msgs in
example : True := by total_cases

/-- error: total_cases: the generator is not a `match` application -/
#guard_msgs in
example : Palamedes.PGen.total (Palamedes.PGen.pure (2 : Nat)) := by total_cases

-- A `match`, but on a closed term rather than a bound variable: there is no hypothesis to case on,
-- so the tactic declines rather than casing something that is not a variable.
/-- error: total_cases: no discriminant is a local hypothesis to case on -/
#guard_msgs in
example : Palamedes.PGen.total
    (match (2 : Nat) with
      | 0 => Palamedes.PGen.pure 0
      | _ + 1 => Palamedes.PGen.pure 1) := by
  total_cases
