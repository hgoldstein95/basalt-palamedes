/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: all-twos list (fold)

Synthesizes `genAllTwosFold : G (List Nat)` for `isAllTwosFold`, the fold-spelled twin of
`isAllTwos` via `List.fold`, exercising a different search path than the structurally recursive
sibling.
-/

open Palamedes

namespace AllTwosFold

@[simp]
def isAllTwosFold (xs : List Nat) : Bool :=
  List.fold true (fun x b => x == 2 && b) xs

def genAllTwosFold [Gen G] : G (List Nat) := by
  generator_search (fun xs => isAllTwosFold xs = true)

end AllTwosFold
