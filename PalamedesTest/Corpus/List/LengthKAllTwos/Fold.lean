/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace LengthKAllTwosFold

@[simp]
def isLengthKAllTwosFold (k : Nat) (xs : List Nat) :=
  List.fold 0 (fun _ b => b + 1) xs = k ∧ List.fold true (fun x b => x == 2 && b) xs

def genLengthKAllTwosFold (k : Nat) : PGen (List Nat) := by
  generator_search (fun xs => isLengthKAllTwosFold k xs = true)

end LengthKAllTwosFold
