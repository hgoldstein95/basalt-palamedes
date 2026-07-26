/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Derive
import Palamedes.CaseSplit

/-!
# The STLC `Ty` datatype layer

STLC types, `derive_palamedes`d, plus a hand-tuned `arbTy` on top of the derived layer with its
case-analysis synthesis rules (`s_arbTy`, `s_caseTy`) and totality facts.
-/

section TypeDef

inductive Ty : Type where
  | unit
  | arrow (τ₁ τ₂ : Ty)
  deriving DecidableEq, Repr

end TypeDef

derive_palamedes Ty

namespace Palamedes

open Palamedes.PGen

namespace PGen

@[irreducible]
def arbTy : PGen Ty := Ty.unfold
  (fun d _ => frequency
    [(2 + 3 * d, pure TyF.unit),
     (1, pure (TyF.arrow PUnit.unit PUnit.unit))])
  PUnit.unit

def caseTy
    (τ : Ty)
    (gu : (τ = Ty.unit) → PGen α)
    (ga : (τ₁ τ₂ : Ty) → (τ = Ty.arrow τ₁ τ₂) → PGen α) :
    PGen α :=
  match τ with
  | .unit => gu rfl
  | .arrow τ₁ τ₂ => (ga τ₁ τ₂ rfl)

/-- The failure-free twin, so `total_Ty_caseTy` has a **generator** to hand `.val` back.

Unlike `X.total_cases`, the case split cannot simply move inside `TGen.mk` here. `τ` is runtime
data, so the `match` cannot reduce; and `gu`/`ga`'s types mention `τ`, so a `match τ with` in the
witness *generalizes them too*, leaving `(hu ⋯).val` inside a matcher arm where `hu` is the arm's own
binder and nothing can project it. The emitted generator then carries `Subtype.val` and `PGen.total`
into the term. Naming the twin moves the match into a constant that is generator code by
construction, and leaves the `.val`s applied to `gu`/`ga` at the *use* site, where they are concrete
lambdas and reduce. Same reason `TGen.elements` exists. -/
def TGen.caseTy
    (τ : Ty)
    (gu : (τ = Ty.unit) → TGen α)
    (ga : (τ₁ τ₂ : Ty) → (τ = Ty.arrow τ₁ τ₂) → TGen α) :
    TGen α :=
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
theorem someSupport_arbTy :
    someSupport arbTy = fun _ => True := by
  simp only [arbTy, Ty.someSupport_unfold]
  generalize (0 : Nat) = d
  funext v
  induction v generalizing d with
  | unit =>
    simp only [Ty.unfold_support, eq_iff_iff, iff_true, someSupport_frequency]
    exact ⟨2 + 3 * d, pure TyF.unit, by simp, by omega, by simp⟩
  | arrow τ₁ τ₂ ih₁ ih₂ =>
    simp only [Ty.unfold_support, eq_iff_iff, iff_true]
    refine ⟨PUnit.unit, PUnit.unit, ?_, of_eq_true (ih₁ (d + 1)), of_eq_true (ih₂ (d + 1))⟩
    simp only [someSupport_frequency]
    exact ⟨1, pure (TyF.arrow PUnit.unit PUnit.unit), by simp, by omega, by simp⟩

@[simp]
theorem support_Ty_caseTy
    {gu : (τ = Ty.unit) → PGen α}
    {ga : (τ₁ τ₂ : Ty) → (τ = Ty.arrow τ₁ τ₂) → PGen α} :
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
    {unitCase : (τ = .unit) → PGen α}
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

/-- The step generator's `TGen` twin, written out, with the `unfold arbTy` confined to the proof —
not `by simp only [arbTy]; apply Ty.total_unfold; …`, which is what this was.

`arbTy` is `@[irreducible]`, so the goal genuinely has to be opened; the question is only *where*.
Opened by `simp only` in tactic mode the whole witness ends up under an `Eq.mpr`, and an `Eq.mpr` in
the **data** path stops `.val` from projecting. At the `Palamedes.PGen` carrier nothing looked at the
witness so nothing showed; at `[Gen G] : G _` the witness *is* the emitted generator, and
`genWellScoped` printed this one node as a 150-line `Eq.mpr … ⟨…, congrFun' (congrFun' (congrArg …))⟩`
congruence tree in a term whose whole purpose is to be read and pasted.

Same shape as `total_arbLabel`, which is `@[irreducible]` for the same reason. -/
@[total]
def total_arbTy : total arbTy :=
  ⟨TGen.Ty.unfold
      (fun d _ => TGen.frequency
        [(2 + 3 * d, TGen.pure TyF.unit),
         (1, TGen.pure (TyF.arrow PUnit.unit PUnit.unit))])
      PUnit.unit,
   by
     unfold arbTy
     exact (_root_.Ty.total_unfold
       (g := fun d _ => frequency
         [(2 + 3 * d, pure TyF.unit),
          (1, pure (TyF.arrow PUnit.unit PUnit.unit))])
       (b := PUnit.unit) (d₀ := 0)
       fun _d _b =>
         total_frequency
           (totalWeighted_cons (total_pure _)
             (totalWeighted_cons (total_pure _) totalWeighted_nil))).property⟩

/-- The witness is a `match` on `τ` producing `TGen`s — mirroring `caseTy`'s own match — and **not**
`by cases τ`, which is what this was.

`total` is `Type`-valued, so `cases` in tactic mode is `Ty.rec` *in the data path*. The projection
`.val` then has nothing to reduce, and the generator reaches the environment as a recursor
application. At the `Palamedes.PGen` carrier that never showed, because the carrier emits the
optimized generator and the witness is only ever checked; at `G α` the witness **is** the emitted
term, and the code generator rejects it with "does not support recursor `Ty.rec`". `genWellTyped` is
the only generator that reaches this rule, so nothing else in the corpus could have caught it.

This is the same discipline `Total.lean` states for the generic combinators and `X.total_cases` for
the base functor: direct `⟨data, proof⟩`, with tactics confined to the proof. The data is
`TGen.caseTy` rather than a `match` written out here — see its docstring for why the split cannot
just move inside `TGen.mk` the way `total_cases`' can. -/
@[total]
def total_Ty_caseTy
    {gu : (τ = Ty.unit) → PGen α}
    {ga : (τ₁ τ₂ : Ty) → (τ = Ty.arrow τ₁ τ₂) → PGen α}
    (hu : ∀ h, total (gu h))
    (ha : ∀ τ₁ τ₂ h, total (ga τ₁ τ₂ h)) :
    total (PGen.caseTy τ (fun h => gu h) (fun τ₁ τ₂ h => ga τ₁ τ₂ h)) :=
  ⟨TGen.caseTy τ (fun h => (hu h).val) (fun τ₁ τ₂ h => (ha τ₁ τ₂ h).val),
   by cases τ
      · exact (hu rfl).property
      · exact (ha _ _ rfl).property⟩

end Total

end PGen

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
