/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.PGen
import Palamedes.CorrectGen
import Palamedes.Total
import Palamedes.SomeSupport
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Basic

/-!
# Drawing from a list

`elements xs h` draws uniformly from a nonempty list — how a variable is picked from an STLC
context. With its support/`someSupport` facts, the synthesis rule `s_elements_partial`, and its
totality witness.
-/

namespace Palamedes

open Palamedes.PGen

namespace PGen

def elements (xs : List α) (h : xs.length > 0) : PGen α :=
  match xs with
  | x :: xs =>
    match hxs : xs with
    | [] => pure x
    | _ :: _ => pick (pure x) (elements xs (by rw [hxs]; simp))

/-- The failure-free twin, mirroring `elements` structurally — the same relationship `TGen.choose`
and `TGen.arbNat` have to their `PGen` counterparts.

It exists because `total_elements`'s witness has to be a **generator**, and `elements` recurses on a
list that is only known at runtime (an STLC context's `idxsOf`). Assembled instead from
`total_pure`/`total_pick` by structural recursion, the witness is a recursive *proof* term, and
`.val` has nothing to project until the list is a literal — which it never is. `genWellTyped` then
carried `(total_elements …).val` into the emitted term, i.e. `Subtype.val`, `PGen.total` and a
`TGen.mk` where generator code was supposed to be. With the recursion done once here, `.val` is a
projection out of a direct `⟨_, _⟩` and lands on this constant. -/
def TGen.elements (xs : List α) (h : xs.length > 0) : TGen α :=
  match xs with
  | x :: xs =>
    match hxs : xs with
    | [] => TGen.pure x
    | _ :: _ => TGen.pick (TGen.pure x) (TGen.elements xs (by rw [hxs]; simp))

@[simp]
theorem support_elements
    {xs : List α} {v : α} {h : xs.length > 0} :
    v ∈ 〚elements xs h〛↔ v ∈ xs := by
  induction xs with
  | nil => simp_all; contradiction
  | cons x xs ih =>
    match hxs : xs with
    | [] =>
      simp_all [elements]
    | _ :: _ =>
      simp [elements] at ih ⊢
      simp_all

@[simp]
theorem someSupport_elements
    {xs : List α} {v : α} {h : xs.length > 0} :
    someSupport (elements xs h) v ↔ v ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    match hxs : xs with
    | [] =>
      simp_all [elements]
    | _ :: _ =>
      simp [elements] at ih ⊢
      simp_all

namespace CorrectGen

@[extract]
def s_elements_partial [DecidableEq α] (xs : List α) : CorrectGen (fun v => List.elem v xs) :=
  Subtype.mk (assume (xs.length > 0) (fun h => elements xs (by aesop))) <| by
    funext v
    simp [support_elements]
    cases xs <;> simp_all

end CorrectGen

namespace Total

/-- The recursion, done once, in `Prop` — where it is erased. -/
theorem toGen_elements : ∀ (xs : List α) (h : xs.length > 0),
    (TGen.elements xs h).toGen = elements xs h
  | [x], _ => TGen.toGen_pure x
  | x :: y :: ys, _ => by
    -- `show` rather than `simp only [elements]`: both sides' outer `match` reduces on a literal
    -- `cons`, and stopping there is the point — unfolding the *inner* one too leaves two `match`es
    -- to relate instead of a `pick` to descend into.
    show (TGen.pick (TGen.pure x) (TGen.elements (y :: ys) (by simp))).toGen
       = pick (pure x) (elements (y :: ys) (by simp))
    rw [TGen.toGen_pick, TGen.toGen_pure, toGen_elements (y :: ys) (by simp)]

/-- Direct `⟨witness, proof⟩` over `TGen.elements` — the same discipline `Total.lean` states for the
combinator basis, and the reason `TGen.elements` exists. -/
@[total]
def total_elements {xs : List α} {h : xs.length > 0} : PGen.total (elements xs h) :=
  ⟨TGen.elements xs h, toGen_elements xs h⟩

end Total

theorem getElem?_eq_some_iff_indexesOf_getElem?_eq_some
    [BEq α]
    [LawfulBEq α]
    {xs : List α}
    {i : Nat}
    {a : α} :
    xs[i]? = some a ↔ i ∈ (xs.idxsOf a) := by
  rw [List.getElem?_eq_some_iff, List.mem_idxsOf_iff_exists_getElem_pos]
  simp

end PGen

end Palamedes
