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

namespace Palamedes

open Palamedes.PGen

namespace PGen

def elements (xs : List α) (h : xs.length > 0) : PGen α :=
  match xs with
  | x :: xs =>
    match hxs : xs with
    | [] => pure x
    | _ :: _ => pick (pure x) (elements xs (by rw [hxs]; simp))

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

@[total]
def total_elements : ∀ {xs : List α} {h : xs.length > 0}, PGen.total (elements xs h)
  | [_], _ => total_pure _
  | _ :: y :: ys, _ => total_pick (total_pure _) (total_elements (xs := y :: ys) (h := by simp))

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
