/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace AllTwosTreeFold

@[simp]
def isAllTwosFold (t : Palamedes.Tree Nat) : Bool :=
  Palamedes.Tree.fold true (fun bl x br => x == 2 && bl && br) t

def genAllTwosFold : PGen (Palamedes.Tree Nat) := by
  generator_search (fun t => isAllTwosFold t = true)

end AllTwosTreeFold
