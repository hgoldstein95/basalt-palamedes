/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace IncreasingByOneTree

@[simp]
def isIncreasingByOneAux (t : Palamedes.Tree Nat) (prev : Nat) : Bool :=
  match t with
  | .leaf => true
  | .node l x r => x == prev + 1 && isIncreasingByOneAux l x && isIncreasingByOneAux r x

@[simp]
def isIncreasingByOne (t : Palamedes.Tree Nat) : Bool :=
  isIncreasingByOneAux t 0

def genIncreasingByOne : PGen (Palamedes.Tree Nat) := by
  generator_search (fun t => isIncreasingByOne t = true)

end IncreasingByOneTree
