import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Total
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Basic

namespace Palamedes

open Gen

namespace Gen

def elements (xs : List α) (h : xs.length > 0) : Gen α :=
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

namespace CorrectGen

def s_elements_partial [DecidableEq α] (xs : List α) : CorrectGen (fun v => List.elem v xs) :=
  Subtype.mk (assume (xs.length > 0) (fun h => elements xs (by aesop))) <| by
    funext v
    simp [support_elements]
    cases xs <;> simp_all

@[extract]
theorem s_elements_partial_val [DecidableEq α] (xs : List α) :
    (s_elements_partial xs).val
      = assume (xs.length > 0) (fun h => elements xs (of_decide_eq_true h)) := rfl

end CorrectGen

namespace Total

@[simp, aesop safe (rule_sets := [totality])]
theorem total_elements :
    (Gen.total (elements xs h)) := by
  induction xs <;> simp at h
  case cons x xs' ih _ =>
    simp [elements]
    cases xs' <;> simp_all

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

end Gen

end Palamedes
