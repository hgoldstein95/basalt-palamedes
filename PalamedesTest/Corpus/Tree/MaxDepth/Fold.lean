/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: trees bounded by a maximum depth, fold-spelled

Synthesizes `genMaxDepthFold : G (Palamedes.Tree Nat)` from `isMaxDepthFold`, the fold-spelled
twin of `isMaxDepth`.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace MaxDepthFold

@[simp]
def isMaxDepthFold (t : Palamedes.Tree Nat) (n : Nat) : Bool :=
  Palamedes.Tree.fold (fun _ => true) (fun bl _ br s => decide (s > 0) && bl (s - 1) && br (s - 1)) t n

def genMaxDepthFold (n : Nat) [Gen G] : G (Palamedes.Tree Nat) := by
  generator_search (fun t => isMaxDepthFold t n = true)

end MaxDepthFold
