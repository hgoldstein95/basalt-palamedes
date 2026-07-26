/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: complete trees of a given depth, fold-spelled

Synthesizes `genCompleteFold : G (Palamedes.Tree Nat)` from `isCompleteFold`, the fold-spelled
twin of `isComplete`.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace CompleteFold

@[simp]
def isCompleteFold (t : Palamedes.Tree Nat) (n : Nat) : Bool :=
  Palamedes.Tree.fold (fun s => s == 0) (fun bl _ br s => decide (s > 0) && bl (s - 1) && br (s - 1)) t n

def genCompleteFold (n : Nat) [Gen G] : G (Palamedes.Tree Nat) := by
  generator_search (fun t => isCompleteFold t n = true)

end CompleteFold
