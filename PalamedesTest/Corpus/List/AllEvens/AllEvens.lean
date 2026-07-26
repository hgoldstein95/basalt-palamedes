/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: all-evens list (structural)

Synthesizes `genAllEvens : G (List Nat)` for `isAllEvens`, defined by structural recursion on
the list.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace AllEvens

@[simp]
def isAllEvens : List Nat → Bool
  | [] => true
  | x :: xs => x % 2 = 0 && isAllEvens xs

def genAllEvens [Gen G] : G (List Nat) := by
  generator_search (fun xs => isAllEvens xs)

end AllEvens
