/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer
import Palamedes.Sample

/-!
# Corpus: red-black tree without the BST condition, fold-spelled

Synthesizes `genRBTFold : G (Palamedes.Tree (Color × Nat))` from `isRBTFold`, the fold-spelled
twin of `isBadRBT`; runs near a raised `maxHeartbeats`/`maxRecDepth`.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace BadRBTFold

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

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

@[simp]
def isRBTFold (height : Nat) (t : Palamedes.Tree (Color × Nat)) : Bool :=
  isBHFold t height = true ∧ isRRFold t = true

def genRBTFold (height : Nat) [Gen G] : G (Palamedes.Tree (Color × Nat)) := by
  generator_search (fun t => isRBTFold height t = true)

end BadRBTFold
