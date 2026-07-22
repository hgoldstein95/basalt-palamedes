/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: all-evens list (fold)

Synthesizes `genAllEvensFold : PGen (List Nat)` for `isAllEvensFold`, the fold-spelled twin of
`isAllEvens` via `List.fold`, exercising a different search path than the structurally recursive
sibling.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace AllEvensFold

@[simp]
def isAllEvensFold (xs : List Nat) : Bool :=
  List.fold true (fun x b => x % 2 == 0 && b) xs

def genAllEvensFold : PGen (List Nat) := by
  generator_search (fun xs => isAllEvensFold xs = true)

end AllEvensFold
