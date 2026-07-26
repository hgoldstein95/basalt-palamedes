/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: symbolic range (filtering)

Synthesizes `genBetweenLoAndHi lo hi : G (Option Nat)` for `fun n => lo ≤ n ∧ n ≤ hi` with symbolic
bounds, a filtering generator (Basalt-shaped `totalize` + `assume`). Pins the emitted term under
`#guard_msgs`.
-/

open Palamedes

/--
info: Try this:
  [apply] exact PGen.totalize (PGen.assume (decide (lo ≤ hi)) fun h => PGen.choose lo hi)
-/
#guard_msgs in
def genBetweenLoAndHi (lo hi : Nat) [Gen G] : G (Option Nat) := by
  generator_search? (fun n => lo ≤ n ∧ n ≤ hi)
