/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Synthesizer
import Palamedes.Data.Tree
import Palamedes.Data.List
import Palamedes.Data.Nat

/-!
# Failure Diagnosis
-/

open Palamedes

namespace PalamedesTest.Diagnose

/-! ## Coercion refused: the generation target is not the first argument

The coercion unifies the scrutinee-typed argument first, so a recursion spelled with its indices in
front never reads as a fold — the diagnosis states the (otherwise unwritten) contract. -/

@[simp]
def isBSTFlipped : (Nat × Nat) → Palamedes.Tree Nat → Bool := fun ⟨lo, hi⟩ t =>
  match t with
  | .leaf => true
  | .node l x r =>
    (lo ≤ x && x ≤ hi) && isBSTFlipped (lo, x - 1) l && isBSTFlipped (x + 1, hi) r

/--
error: Failed during generator synthesis.
Tactic `aesop` failed, made no progress
Initial goal:
  G : Type → Type
  lo hi : ℕ
  inst✝ : Gen G
  ⊢ CorrectGen fun t => isBSTFlipped (lo, hi) t = true

Unfold synthesis for `Palamedes.Tree` stopped at the coercion: `Palamedes.Tree.coerce_to_fold` could not rewrite this predicate into a `Palamedes.Tree.fold`.
The generation target is `PalamedesTest.Diagnose.isBSTFlipped`'s explicit argument 2; the coercion unifies the `Palamedes.Tree`-typed argument first, so try the recursion with that argument first and any indices after it.
-/
#guard_msgs in
example (lo hi : Nat) [Gen G] : G (Palamedes.Tree Nat) := by
  generator_search (fun t => isBSTFlipped (lo, hi) t = true)

/-! ## Coercion refused: two curried indices

One trailing index is the most the coercion's `congrFun` alternatives handle; the corpus spelling
(`Corpus/Tree/BST`) tuples `lo` and `hi` for exactly this reason. -/

@[simp]
def isBSTCurried : Palamedes.Tree Nat → Nat → Nat → Bool := fun t lo hi =>
  match t with
  | .leaf => true
  | .node l x r =>
    (lo ≤ x && x ≤ hi) && isBSTCurried l lo (x - 1) && isBSTCurried r (x + 1) hi

/--
error: Failed during generator synthesis.
Tactic `aesop` failed, made no progress
Initial goal:
  G : Type → Type
  lo hi : ℕ
  inst✝ : Gen G
  ⊢ CorrectGen fun t => isBSTCurried t lo hi = true

Unfold synthesis for `Palamedes.Tree` stopped at the coercion: `Palamedes.Tree.coerce_to_fold` could not rewrite this predicate into a `Palamedes.Tree.fold`.
`PalamedesTest.Diagnose.isBSTCurried` takes 2 curried arguments after the generation target, and the coercion handles at most one — tuple the indices into a single trailing argument (`PalamedesTest.Diagnose.isBSTCurried t (i, j)`) and match on the tuple in the defining equations.
-/
#guard_msgs in
example (lo hi : Nat) [Gen G] : G (Palamedes.Tree Nat) := by
  generator_search (fun t => isBSTCurried t lo hi = true)

/-! ## A merged conjunction names the first refusing goal, with a caveat

The `∧`-merge splits the predicate before the coercion runs, and in the full pipeline a refused
coercion still falls through to the conversion step — so the named conjunct is the first refusal,
not necessarily the pipeline's actual point of failure, and the message says so. -/

/--
error: Failed during generator synthesis.
Tactic `aesop` failed, made no progress
Initial goal:
  G : Type → Type
  lo hi : ℕ
  inst✝ : Gen G
  ⊢ CorrectGen fun t => isBSTCurried t lo hi = true ∧ isBSTFlipped (lo, hi) t = true

Unfold synthesis for `Palamedes.Tree` stopped at the coercion: `Palamedes.Tree.coerce_to_fold` could not rewrite this predicate into a `Palamedes.Tree.fold`.
`PalamedesTest.Diagnose.isBSTCurried` takes 2 curried arguments after the generation target, and the coercion handles at most one — tuple the indices into a single trailing argument (`PalamedesTest.Diagnose.isBSTCurried t (i, j)`) and match on the tuple in the defining equations.
This is a merged predicate; the culprit for this error may may be a different conjunct or the merge itself.
-/
#guard_msgs in
example (lo hi : Nat) [Gen G] : G (Palamedes.Tree Nat) := by
  generator_search (fun t => isBSTCurried t lo hi = true ∧ isBSTFlipped (lo, hi) t = true)

/-! ## The unfold fires; the failure is below it

The fold coerces and converts, so the diagnosis prints the per-step generator goal the search could
not close — here the arithmetic guard `a1 * 2 == 12`, which no leaf rule solves. -/

@[simp]
def allSix : List Nat → Bool
  | [] => true
  | x :: xs => x * 2 == 12 && allSix xs

/--
error: Failed during generator synthesis.
Tactic `aesop` failed, made no progress
Initial goal:
  G : Type → Type
  inst✝ : Gen G
  ⊢ CorrectGen fun xs => allSix xs = true

Search failed below the unfold while synthesizing the per-step generator: ⏎
  G : Type → Type
  inst✝ : Gen G
  ⊢ (bg : Unit) →
      Unit →
        CorrectGen fun tv =>
          guard (allSix [] = true) = some bg ∧ tv = ListF.nil ∨
            ∃ a1 a2, guard ((a1 * 2 == 12) = true) = some bg ∧ tv = ListF.cons a1 a2
-/
#guard_msgs in
example [Gen G] : G (List Nat) := by
  generator_search (fun xs => allSix xs = true)

/-! ## Recursion over a datatype nothing registered -/

inductive MyTree where
  | leaf
  | node (l : MyTree) (x : Nat) (r : MyTree)

@[simp]
def leafy : MyTree → Bool
  | .leaf => true
  | .node l _ r => leafy l && leafy r

/--
error: Failed during generator synthesis.
Tactic `aesop` failed, made no progress
Initial goal:
  G : Type → Type
  inst✝ : Gen G
  ⊢ CorrectGen fun t => leafy t = true

`PalamedesTest.Diagnose.MyTree` has no `unfold_strategy` entry, so the unfold rule could not fire on `PalamedesTest.Diagnose.leafy`. If `PalamedesTest.Diagnose.MyTree` is a plain recursive datatype, `derive_palamedes PalamedesTest.Diagnose.MyTree` registers everything unfold synthesis needs.
-/
#guard_msgs in
example [Gen G] : G MyTree := by
  generator_search (fun t => leafy t = true)

/-! ## Leaf-shaped predicates: what the rules were matched against

The shared normalization runs before any leaf rule, so when it changes the predicate the user's
spelling is not what was rejected — and when it does not, that fact is worth a sentence too. -/

/--
error: Failed during generator synthesis.
Tactic `aesop` failed, made no progress
Initial goal:
  G : Type → Type
  inst✝ : Gen G
  ⊢ CorrectGen fun n => decide (n % 3 = 0) = true

No search rule matched. The normalizing rules were tried against ⏎
  fun n => n % 3 = 0
rather than the expression as written — if that shape is not the one you meant to expose, rewrite the predicate so normalization preserves it.
-/
#guard_msgs in
example [Gen G] : G Nat := by
  generator_search (fun n => decide (n % 3 = 0) = true)

/--
error: Failed during generator synthesis.
Tactic `aesop` failed, made no progress
Initial goal:
  G : Type → Type
  inst✝ : Gen G
  ⊢ CorrectGen fun n => n * 2 = 4

No search rule matched this predicate.
-/
#guard_msgs in
example [Gen G] : G Nat := by
  generator_search (fun n => n * 2 = 4)

/-! ## A disjunction is diagnosed disjunct by disjunct

`s_pick` splits a top-level `∨` into one search per disjunct, so the diagnosis names the disjunct
that fails alone and recurses into it. -/

/--
error: Failed during generator synthesis.
Tactic `aesop` failed, made no progress
Initial goal:
  G : Type → Type
  inst✝ : Gen G
  ⊢ CorrectGen fun xs => xs = [1] ∨ allSix xs = true

`s_pick` splits the disjunction, and its right disjunct
  fun xs => allSix xs = true
is the one the search cannot close.

Search failed below the unfold while synthesizing the per-step generator: ⏎
  G : Type → Type
  inst✝ : Gen G
  ⊢ (bg : Unit) →
      Unit →
        CorrectGen fun tv =>
          guard (allSix [] = true) = some bg ∧ tv = ListF.nil ∨
            ∃ a1 a2, guard ((a1 * 2 == 12) = true) = some bg ∧ tv = ListF.cons a1 a2
-/
#guard_msgs in
example [Gen G] : G (List Nat) := by
  generator_search (fun xs => xs = [1] ∨ allSix xs = true)

/-! ## A shape the unfold rule does not fire on -/

/--
error: Failed during generator synthesis.
Tactic `aesop` failed, made no progress
Initial goal:
  G : Type → Type
  inst✝ : Gen G
  ⊢ CorrectGen fun xs => xs ≠ []

`List` is registered for unfold synthesis, but the unfold rule fires only on predicates shaped `fun x => _ = _` or `fun x => _ ∧ _` — this predicate is neither.
-/
#guard_msgs in
example [Gen G] : G (List Nat) := by
  generator_search (fun xs => xs ≠ [])

end PalamedesTest.Diagnose
