/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: all-twos list (structural)

Synthesizes `genAllTwos : PGen (List Nat)` for `isAllTwos`, defined by structural recursion on the
list.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace AllTwos

@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

def genAllTwos : PGen (List Nat) := by
  generator_search (fun xs => isAllTwos xs)

end AllTwos
