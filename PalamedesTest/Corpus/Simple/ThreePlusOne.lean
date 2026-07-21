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
  [apply] exact pure 4
-/
#guard_msgs in
def genThreePlusOne : PGen Nat := by
  generator_search? (fun b => ∃ a, a = 3 ∧ b = a + 1)
