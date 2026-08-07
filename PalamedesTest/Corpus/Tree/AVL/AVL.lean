/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: AVL trees

Synthesizes `genAVL : G (Option (Palamedes.Tree Nat))` from `isAVL`, which conjoins `isBST`
(bounded-key BST shape) and `isBalanced` (height-bounded); a filtering generator.
-/

open Palamedes

namespace AVL

@[simp]
def isBST (t : Palamedes.Tree Nat) : Nat × Nat →  Bool := fun (lo, hi) =>
  match t with
  | .leaf => true
  | .node l x r =>
    (lo <= x && x <= hi) &&
    isBST l ⟨lo, x - 1⟩ &&
    isBST r ⟨x + 1, hi⟩

@[simp]
def isBalanced (t : Palamedes.Tree Nat) (height : Nat) : Bool :=
  match t with
  | .leaf => height <= 1
  | .node l _ r =>
    height > 0 &&
    isBalanced l (height - 1) &&
    isBalanced r (height - 1)

@[simp]
def isAVL (height lo hi : Nat) (t : Palamedes.Tree Nat) : Bool :=
  isBalanced t height && isBST t (lo, hi)

/--
info: Try this:
  [apply] exact
    Tree.unfoldGo
      (fun d x =>
        if x.2.1 = 0 then OptionT.pure TreeF.leaf
        else
          if Nat.pred x.2.1 = 0 then
            OptionT.bind
              (if h : decide (x.2.2.1 ≤ x.2.2.2) = true then
                frequency
                  [(1, fun x => OptionT.pure TreeF.leaf),
                    (1, fun x_1 =>
                      OptionT.bind (TGen.choose x.2.2.1 x.2.2.2).run fun a =>
                        OptionT.pure (TreeF.node (PUnit.unit, PUnit.unit) a (PUnit.unit, PUnit.unit)))]
              else OptionT.pure TreeF.leaf)
              fun a =>
              match a with
              | TreeF.leaf => OptionT.pure TreeF.leaf
              | TreeF.node a1 a2 a3 =>
                OptionT.pure (TreeF.node (a1, x.2.1 - 1, x.2.2.1, a2 - 1) a2 (a3, x.2.1 - 1, a2 + 1, x.2.2.2))
          else
            if h : decide (x.2.2.1 ≤ x.2.2.2) = true then
              OptionT.bind (TGen.choose x.2.2.1 x.2.2.2).run fun a =>
                OptionT.pure
                  (TreeF.node ((PUnit.unit, PUnit.unit), x.2.1 - 1, x.2.2.1, a - 1) a
                    ((PUnit.unit, PUnit.unit), x.2.1 - 1, a + 1, x.2.2.2))
            else pure none)
      0 ((PUnit.unit, PUnit.unit), height, lo, hi)
---
info: @[correct] AVL.genAVL: emitted sound_complete
-/
#guard_msgs in
@[correct] def genAVL (height lo hi : Nat) [Gen G] : G (Option (Palamedes.Tree Nat)) := by
  generator_search? (fun t => isAVL height lo hi t = true)

/-- info: 'AVL.genAVL.sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms genAVL.sound_complete

end AVL
