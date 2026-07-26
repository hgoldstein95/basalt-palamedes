/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer
import Palamedes.Data.Color

/-!
# Corpus: red-black trees

Synthesizes `genRBT : G (Option (Palamedes.Tree (Color × Nat)))` from `isRBT`, which conjoins
`isRR` (no red-red violation), `isBST` (bounded-key ordering), and `isBH` (equal black height); a
filtering generator run near a raised `maxHeartbeats`/`maxRecDepth`.
-/

open Palamedes

namespace RBT

@[simp]
def isRRAux : Palamedes.Tree (Color × α) → Bool → Bool := λ t isRedChild =>
 match t with
 | .leaf => true
 | .node l c r => if c.fst == .red then !isRedChild && isRRAux l true && isRRAux r true else isRRAux l false && isRRAux r false

@[simp]
def isRR : Palamedes.Tree (Color × α) → Bool := λ t => isRRAux t false

@[simp]
def isBH : Palamedes.Tree (Color × α) → Nat → Bool := λ t height =>
 match t with
 | .leaf => height == 0
 | .node l c r => if c.fst == .red then isBH l height && isBH r height else height >= 0 && isBH l (height - 1) && isBH r (height - 1)

@[simp]
def isBST : Palamedes.Tree (α × Nat) → (Nat × Nat) → Bool := λ t ⟨lo, hi⟩ =>
  match t with
  | .leaf => true
  | .node l (_, x) r => (lo <= x && x <= hi) && isBST l ⟨lo, x - 1⟩ && isBST r ⟨x + 1, hi⟩

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

@[simp]
def isRBT : Palamedes.Tree (Color × Nat) → Nat → Nat → Nat → Bool := λ t height lo hi =>
  isRR t && isBST t (lo, hi) && isBH t height

-- Filtering, declared in the return type.
--
-- Tagged `@[correct]` as the regression for the `someSupport` bridge's **bound-scrutinee** case.
-- `genAVL` guards the recursive-and-filtering combination, but its match arms are bare `pure`s that
-- simp equates on both sides without ever needing the scrutinee; RBT's carry `ite`s on the matched
-- colour, so the bridge has to case-split a `match` on a variable bound by an `∃` *inside* the goal.
-- Nothing else in the corpus reaches that branch of the script.
/-- info: @[correct] RBT.genRBT: emitted sound_complete -/
#guard_msgs in
@[correct] def genRBT (height lo hi : Nat) [Gen G] :
    G (Option (Palamedes.Tree (Color × Nat))) := by
  generator_search (fun t => isRBT t height lo hi)

/-- info: 'RBT.genRBT.sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms genRBT.sound_complete

end RBT
