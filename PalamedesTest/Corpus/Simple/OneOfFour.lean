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
  [apply] exact PGen.oneOf [pure 1, pure 2, pure 3, pure 4]
-/
#guard_msgs in
def genSmall : PGen Nat := by
  generator_search? (fun a => a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4)
