/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: Binary Search Trees
-/

open Palamedes

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
    Tree.unfoldGo
      (fun d x => do
        let a ←
          if hb : decide (x.2.1 ≤ x.2.2) = true then
              frequency
                [(1, fun x => pure TreeF.leaf),
                  (1, fun x_1 => do
                    let a ← chooseNat x.2.1 x.2.2
                    pure (TreeF.node PUnit.unit a PUnit.unit))]
            else pure TreeF.leaf
        match a with
          | TreeF.leaf => pure TreeF.leaf
          | TreeF.node a1 a2 a3 => pure (TreeF.node (a1, x.2.1, a2 - 1) a2 (a3, a2 + 1, x.2.2)))
      0 (PUnit.unit, lo, hi)
-/
#guard_msgs in
def genBST (lo hi : Nat) [Gen G] : G (Palamedes.Tree Nat) := by
  generator_search? (fun t => isBST t (lo, hi) = true)

end BST
