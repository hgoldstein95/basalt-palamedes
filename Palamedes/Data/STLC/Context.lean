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

/-! ## The primitive

Drawing from a list cannot fail, so `elements` is spelled at the failure-free interface `TGen` and
its `PGen` form is `TGen.toGen` of it. In `Palamedes.TGen` beside the core algebra, not
`Palamedes.PGen.TGen`; see the section header in `Data/Nat.lean` for what the second spelling costs.

The direction matters more here than for a non-recursive primitive. `elements` recurses on a list
that is only known at runtime (an STLC context's `idxsOf`), so a witness assembled from
`total_pure`/`total_pick` by structural recursion is a recursive *proof* term whose `.val` has
nothing to project until the list is a literal — which it never is. `genWellTyped` would then carry
`Subtype.val`, `PGen.total` and a `TGen.mk` into the emitted term where generator code belongs. With
the recursion written once, at `TGen`, `.val` is a projection out of a direct `⟨_, rfl⟩` and lands on
this constant. -/

namespace TGen

/-- Draw uniformly from a nonempty list. -/
def elements (xs : List α) (h : xs.length > 0) : TGen α :=
  match xs with
  | x :: xs =>
    match hxs : xs with
    | [] => TGen.pure x
    | _ :: _ => TGen.pick (TGen.pure x) (TGen.elements xs (by rw [hxs]; simp))

end TGen

namespace PGen

def elements (xs : List α) (h : xs.length > 0) : PGen α := (TGen.elements xs h).toGen

/-! `elements`' defining equations, restated at `PGen`: the recursion computes at `TGen`, and these
carry it across the coercion for the `support` proofs below. -/

@[simp] theorem elements_singleton (x : α) (h) : elements [x] h = pure x := rfl

@[simp] theorem elements_cons_cons (x y : α) (ys : List α) (h) :
    elements (x :: y :: ys) h = pick (pure x) (elements (y :: ys) (by simp)) := by
  show (TGen.pick (TGen.pure x) (TGen.elements (y :: ys) (by simp))).toGen = _
  rw [TGen.toGen_pick, TGen.toGen_pure]
  rfl

@[simp]
theorem support_elements
    {xs : List α} {v : α} {h : xs.length > 0} :
    v ∈ 〚elements xs h〛↔ v ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    match hxs : xs with
    | [] => simp_all
    | _ :: _ =>
      simp at ih ⊢
      simp_all

@[simp]
theorem someSupport_elements
    {xs : List α} {v : α} {h : xs.length > 0} :
    someSupport (elements xs h) v ↔ v ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    match hxs : xs with
    | [] => simp_all
    | _ :: _ =>
      simp at ih ⊢
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

/-- Direct `⟨witness, proof⟩` over `TGen.elements` — the same discipline `Total.lean` states for the
combinator basis. `elements` is that generator coerced, so the equation is `rfl`. -/
@[total]
def total_elements {xs : List α} {h : xs.length > 0} : PGen.total (elements xs h) :=
  ⟨TGen.elements xs h, rfl⟩

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
