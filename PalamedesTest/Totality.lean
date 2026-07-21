/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer.Totality

/-!
# `total_cases` regression

`total_cases` is what keeps the totality witness in the *data* path: it cases the `match`
discriminant directly, so the `match` iota-reduces and no `Eq.rec` cast is created. `PalamedesTest/
Extract.lean` audits the consequence; this file pins the tactic's own preconditions.

All three failures matter for the same reason. When `total_cases` declines, the `totality` cascade
falls through to `split`, which *does* close the goal — while leaving the cast that
`PalamedesTest/Extract.lean` then rejects. So a precondition silently drifting is a failure that
surfaces two modules away, as extraction residue rather than as a tactic error.
-/

open Palamedes Palamedes.PGen

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
