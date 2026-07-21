/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace MaxDepth

@[simp]
def isMaxDepth (t : Palamedes.Tree α) (n : Nat) : Bool :=
  match t with
  | .leaf => true
  | .node l _ r =>
    n > 0 &&
    isMaxDepth l (n - 1) &&
    isMaxDepth r (n - 1)

def genComplete (n : Nat) : PGen (Palamedes.Tree Nat) := by
  generator_search (fun t => isMaxDepth t n = true)

end MaxDepth
