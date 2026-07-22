/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: all-twos tree

Synthesizes `genAllTwos : PGen (Palamedes.Tree Nat)` from the structurally recursive predicate
`isAllTwos`, which holds when every node label is `2`.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace AllTwosTree

@[simp]
def isAllTwos : Palamedes.Tree Nat → Bool
  | .leaf => true
  | .node l x r => x = 2 && isAllTwos l && isAllTwos r

def genAllTwos : PGen (Palamedes.Tree Nat) := by
  generator_search (fun t => isAllTwos t)

end AllTwosTree
