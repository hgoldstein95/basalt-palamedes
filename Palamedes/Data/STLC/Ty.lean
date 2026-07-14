import Palamedes.Derive
import Palamedes.CaseSplit

section TypeDef

inductive Ty : Type where
  | unit
  | arrow (τ₁ τ₂ : Ty)
  deriving DecidableEq, Repr

end TypeDef

derive_palamedes Ty

namespace Palamedes

open Gen

namespace Gen

@[irreducible]
def arbTy : Gen Ty := Ty.unfold
  (fun d _ => frequency
    [(2 + 3 * d, pure TyF.unit),
     (1, pure (TyF.arrow PUnit.unit PUnit.unit))])
  PUnit.unit

def caseTy
    (τ : Ty)
    (gu : (τ = Ty.unit) → Gen α)
    (ga : (τ₁ τ₂ : Ty) → (τ = Ty.arrow τ₁ τ₂) → Gen α) :
    Gen α :=
  match τ with
  | .unit => gu rfl
  | .arrow τ₁ τ₂ => (ga τ₁ τ₂ rfl)

@[simp]
theorem support_arbTy :
    support arbTy = fun _ => True := by
  simp only [arbTy, Ty.support_unfold]
  generalize (0 : Nat) = d
  funext v
  induction v generalizing d with
  | unit =>
    simp only [Ty.unfold_support, eq_iff_iff, iff_true, Support.support_frequency]
    exact ⟨2 + 3 * d, pure TyF.unit, by simp, by omega, by simp⟩
  | arrow τ₁ τ₂ ih₁ ih₂ =>
    simp only [Ty.unfold_support, eq_iff_iff, iff_true]
    refine ⟨PUnit.unit, PUnit.unit, ?_, of_eq_true (ih₁ (d + 1)), of_eq_true (ih₂ (d + 1))⟩
    simp only [Support.support_frequency]
    exact ⟨1, pure (TyF.arrow PUnit.unit PUnit.unit), by simp, by omega, by simp⟩

@[simp]
theorem support_Ty_caseTy
    {gu : (τ = Ty.unit) → Gen α}
    {ga : (τ₁ τ₂ : Ty) → (τ = Ty.arrow τ₁ τ₂) → Gen α} :
    support (caseTy
            τ
            (fun h => gu h)
            (fun τ₁ τ₂ h => ga τ₁ τ₂ h)) =
    (fun a =>
      (∃ h : τ = Ty.unit, a ∈ 〚gu h〛) ∨
      (∃ (τ₁ τ₂ : Ty) (h : τ = Ty.arrow τ₁ τ₂), a ∈ 〚ga τ₁ τ₂ h〛)) := by
  funext
  simp
  apply Iff.intro
  . intro h
    cases τ <;> aesop
  . intro h
    cases h <;> aesop

@[gen_congr]
theorem support_caseTy_congr
    {unitCase : (τ = .unit) → Gen α}
    {h_unitCase : ∀ {h}, support (unitCase h) = support (unitCase' h)}
    {h_arrowCase : ∀ {τ₁ τ₂ h}, support (arrowCase τ₁ τ₂ h) = support (arrowCase' τ₁ τ₂ h)} :
    support (caseTy τ unitCase arrowCase) = support (caseTy τ unitCase' arrowCase') := by
  aesop

namespace CorrectGen

@[extract, aesop safe apply (rule_sets := [synthesis])]
def s_arbTy : @CorrectGen Ty (fun _ => True) :=
  Subtype.mk arbTy <| by
    funext v
    simp

@[extract, case_split]
def s_caseTy
    {Q : α → Prop}
    {P : α → Ty → Prop}
    (τ : Ty)
    (h : ∀ {a}, P a τ = Q a)
    (gu : CorrectGen (fun a => P a .unit))
    (ga : (τ₁ τ₂ : Ty) → CorrectGen (fun a => P a (.arrow τ₁ τ₂))) :
    CorrectGen Q :=
    Subtype.mk
      (caseTy
        τ
        (fun _ => gu.val)
        (fun τ₁ τ₂ _ => (ga τ₁ τ₂).val)) <| by
    match τ with
    | .unit => simp [gu.property, h]
    | .arrow τ₁ τ₂ => simp [(ga τ₁ τ₂).property, h, caseTy]

end CorrectGen

namespace Total

@[simp, total]
theorem total_arbTy : total arbTy := by
  simp only [Gen.arbTy]
  apply _root_.Ty.total_unfold
  intro _d _b
  exact total_frequency
    (totalWeighted_cons (total_pure _) (totalWeighted_cons (total_pure _) totalWeighted_nil))

@[simp, total]
theorem total_Ty_caseTy
    {gu : (τ = Ty.unit) → Gen α}
    {ga : (τ₁ τ₂ : Ty) → (τ = Ty.arrow τ₁ τ₂) → Gen α}
    (hu : ∀ h, total (gu h))
    (ha : ∀ τ₁ τ₂ h, total (ga τ₁ τ₂ h)) :
    total (Gen.caseTy τ (fun h => gu h) (fun τ₁ τ₂ h => ga τ₁ τ₂ h))
  := by
  cases τ
  case unit => exact hu rfl
  case arrow τ₁ τ₂ => simp_all only [Gen.caseTy]

end Total

end Gen

end Palamedes

namespace PrettyPrint

def Ty.toString : Ty → String
  | .unit => "()"
  | .arrow τ₁ τ₂ => s!"({Ty.toString τ₁} → {Ty.toString τ₂})"

instance : ToString Ty where
  toString := Ty.toString

end PrettyPrint

theorem Ty.deforest_eq
    {b b_unit : β}
    {b_arrow : Ty → Ty → β} :
    Ty.rec b_unit (fun τ₁ τ₂ _ _ => b_arrow τ₁ τ₂) τ = b ↔
    Ty.rec (b_unit = b) (fun τ₁ τ₂ _ _ => b_arrow τ₁ τ₂ = b) τ := by
  induction τ <;> aesop

theorem Ty.as_or
  {P_unit : Prop}
  {P_arrow : Ty → Ty → Prop} :
  Ty.rec P_unit (fun τ₁ τ₂ _ _ => P_arrow τ₁ τ₂) τ ↔
  (τ = .unit ∧ P_unit) ∨ (∃ τ₁ τ₂, τ = .arrow τ₁ τ₂ ∧ P_arrow τ₁ τ₂) := by
  induction τ <;> aesop
