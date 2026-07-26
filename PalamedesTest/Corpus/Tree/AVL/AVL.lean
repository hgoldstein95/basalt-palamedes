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

set_option maxHeartbeats 1000000

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

-- Tagged `@[correct]` as the regression for the `someSupport` bridge over a **filtering,
-- recursive** generator, which is the combination that stresses it. Nothing else in the corpus
-- covers that: the other filtering generators carrying laws are non-recursive, and the recursive
-- ones are total.
/-- info: @[correct] AVL.genAVL: emitted sound_complete -/
#guard_msgs in
@[correct] def genAVL (height lo hi : Nat) [Gen G] : G (Option (Palamedes.Tree Nat)) := by
  generator_search (fun t => isAVL height lo hi t = true)

/-- info: 'AVL.genAVL.sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms genAVL.sound_complete

end AVL
