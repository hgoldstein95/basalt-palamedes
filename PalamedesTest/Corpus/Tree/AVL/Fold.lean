/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace AVLFold

@[simp]
def isAVLFold (height lo hi : Nat) (t : Palamedes.Tree Nat) : Bool :=
  Palamedes.Tree.fold
      (fun _ => true)
      (fun bl x br bounds =>
        match bounds with
        | (sl, sr) => decide (sl ≤ x) && decide (x ≤ sr)
          && bl (sl, x - 1) && br (x + 1, sr))
      t (lo, hi) = true
    ∧
    Palamedes.Tree.fold
      (fun h => decide (h ≤ 1))
      (fun bl _ br h => decide (h > 0) && bl (h - 1) && br (h - 1))
      t height

set_option maxHeartbeats 1000000

def genAVLFold (height lo hi : Nat) [Gen G] : G (Option (Palamedes.Tree Nat)) := by
  generator_search (fun t => isAVLFold height lo hi t = true)

end AVLFold
