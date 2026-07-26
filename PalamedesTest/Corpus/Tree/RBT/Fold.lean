/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer
import Palamedes.Sample

/-!
# Corpus: red-black trees, fold-spelled

Synthesizes `genRBTFold : G (Option (Palamedes.Tree (Color × Nat)))` from `isRBTFold`, the
fold-spelled twin of `isRBT`; a filtering generator run near a raised `maxHeartbeats`/`maxRecDepth`.
-/

open Palamedes

namespace RBTFold

@[simp]
def isRRFold (t : Palamedes.Tree (Color × α)) : Bool :=
  Palamedes.Tree.fold
    (fun _ => true)
    (fun bl c br isRedChild => if c.fst == .red then !isRedChild && bl true && br true else bl false && br false)
    t
    false

@[simp]
def isBHFold (t : Palamedes.Tree (Color × α)) (height : Nat) : Bool :=
  Palamedes.Tree.fold
    (fun h => h == 0)
    (fun bl c br h => if c.fst == .red then bl h && br h else h >= 0 && bl (h - 1) && br (h - 1))
    t
    height

@[simp]
def isBSTFold (t : Palamedes.Tree (α × Nat)) : Nat × Nat -> Bool := fun (lo, hi) =>
  Palamedes.Tree.fold
        (fun _ => true)
        (fun bl x br s =>
          match s with
          | (sl, sr) => (decide (sl ≤ x.snd) && decide (x.snd ≤ sr)) && bl (sl, x.snd - 1) && br (x.snd + 1, sr))
        t (lo, hi)

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

@[simp]
def isRBTFold (height lo hi : Nat) (t : Palamedes.Tree (Color × Nat)) : Bool :=
  isBHFold t height = true ∧ isRRFold t = true ∧ isBSTFold t (lo, hi) = true

def genRBTFold (height lo hi : Nat) [Gen G] :
    G (Option (Palamedes.Tree (Color × Nat))) := by
  generator_search (fun t => isRBTFold height lo hi t = true)

end RBTFold
