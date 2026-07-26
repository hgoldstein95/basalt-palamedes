/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: length k and all-twos (fold)

Synthesizes `genLengthKAllTwosFold k : G (List Nat)` for `isLengthKAllTwosFold`, the
fold-spelled twin of `isLengthKAllTwos` via `List.fold`, exercising a different search path than
the structurally recursive sibling.
-/

open Palamedes

namespace LengthKAllTwosFold

@[simp]
def isLengthKAllTwosFold (k : Nat) (xs : List Nat) :=
  List.fold 0 (fun _ b => b + 1) xs = k ∧ List.fold true (fun x b => x == 2 && b) xs

def genLengthKAllTwosFold (k : Nat) [Gen G] : G (List Nat) := by
  generator_search (fun xs => isLengthKAllTwosFold k xs = true)

end LengthKAllTwosFold
