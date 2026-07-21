/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace Complete

@[simp]
def isComplete (t : Palamedes.Tree α) (n : Nat) : Bool :=
  match t with
  | .leaf => n == 0
  | .node l _ r =>
    n > 0 &&
    isComplete l (n - 1) &&
    isComplete r (n - 1)

def genComplete (n : Nat) : PGen (Palamedes.Tree Nat) := by
  generator_search (fun t => isComplete t n = true)

end Complete
