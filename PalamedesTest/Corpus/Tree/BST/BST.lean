/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: binary search trees

Synthesizes `genBST : PGen (Palamedes.Tree Nat)` from `isBST`, the bounded-key BST predicate.
Pins the emitted term under `#guard_msgs`.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace BST

@[simp]
def isBST : Palamedes.Tree Nat → (Nat × Nat) → Bool := fun t ⟨lo, hi⟩ =>
  match t with
  | .leaf => true
  | .node l x r =>
    (lo <= x && x <= hi) &&
    isBST l ⟨lo, x - 1⟩ &&
    isBST r ⟨x + 1, hi⟩

/--
info: Try this:
  [apply] exact
    Tree.unfold
      (fun d p => do
        let tv ←
          if h : decide (p.2.1 ≤ p.2.2) = true then
              PGen.oneOf
                [pure TreeF.leaf, do
                  let a ← choose p.2.1 p.2.2
                  pure (TreeF.node PUnit.unit a PUnit.unit)]
            else pure TreeF.leaf
        match tv with
          | TreeF.leaf => pure TreeF.leaf
          | TreeF.node a1 a2 a3 => pure (TreeF.node (a1, p.2.1, a2 - 1) a2 (a3, a2 + 1, p.2.2)))
      (PUnit.unit, lo, hi)
-/
#guard_msgs in
def genBST (lo hi : Nat) : PGen (Palamedes.Tree Nat) := by
  generator_search? (fun t => isBST t (lo, hi) = true)

end BST
