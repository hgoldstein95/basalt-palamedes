/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

/--
info: Try this:
  [apply] exact totalize (assume (decide (lo ≤ hi)) fun h => choose lo hi)
-/
#guard_msgs in
def genBetweenLoAndHi (lo hi : Nat) [Gen G] : G (Option Nat) := by
  generator_search? (fun n => lo ≤ n ∧ n ≤ hi)
