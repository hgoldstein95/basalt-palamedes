/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: binary search trees, fold-spelled

Synthesizes `genBSTFold : G (Palamedes.Tree Nat)` from `isBSTFold`, the fold-spelled twin of
`isBST`.
-/

open Palamedes

namespace BSTFold

@[simp]
def isBSTFold (lo hi : Nat) (t : Palamedes.Tree Nat) : Bool :=
  Palamedes.Tree.fold
        (fun _ => true)
        (fun bl x br s =>
          match s with
          | (sl, sr) => (decide (sl ≤ x) && decide (x ≤ sr)) && bl (sl, x - 1) && br (x + 1, sr))
        t (lo, hi)

def genBSTFold (lo hi : Nat) [Gen G] : G (Palamedes.Tree Nat) := by
  generator_search (fun t  => isBSTFold lo hi t = true)

end BSTFold
