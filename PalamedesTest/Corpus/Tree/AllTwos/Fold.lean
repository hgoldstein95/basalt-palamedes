/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: all-twos tree, fold-spelled

Synthesizes `genAllTwosFold : G (Palamedes.Tree Nat)` from `isAllTwosFold`, the fold-spelled
twin of `isAllTwos` written as an explicit `Tree.fold`.
-/

open Palamedes

namespace AllTwosTreeFold

@[simp]
def isAllTwosFold (t : Palamedes.Tree Nat) : Bool :=
  Palamedes.Tree.fold true (fun bl x br => x == 2 && bl && br) t

def genAllTwosFold [Gen G] : G (Palamedes.Tree Nat) := by
  generator_search (fun t => isAllTwosFold t = true)

end AllTwosTreeFold
