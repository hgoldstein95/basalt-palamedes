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

/-! ## The type generator

`arbTy` never filters, so it is spelled at the failure-free interface `TGen` and its `PGen` form is
`TGen.toGen` of it; see the section header in `Data/Nat.lean` for why the twin belongs in
`Palamedes.TGen` and not `Palamedes.PGen.TGen`. `total_arbTy`'s witness is then the definition
itself, and the depth-decaying weights below are stated in exactly one place. -/

namespace TGen

/-- An arbitrary type. The `unit` weight grows with depth while `arrow`'s stays at `1`, so the
branching process is subcritical and the expected size is finite. -/
def arbTy : TGen Ty := TGen.Ty.unfold
  (fun d _ => TGen.frequency
    [(2 + 3 * d, TGen.pure TyF.unit),
     (1, TGen.pure (TyF.arrow PUnit.unit PUnit.unit))])
  PUnit.unit

end TGen

namespace PGen

/-- `@[irreducible]` so the optimizer treats a type draw as an opaque primitive rather than
descending into it and flattening its `frequency` into the enclosing choice. -/
@[irreducible]
def arbTy : PGen Ty := TGen.arbTy.toGen

/-- Case analysis on a `Ty` scrutinee, as a generator combinator.

The branches are deliberately **non-dependent** — neither receives the equation (`τ = .unit`,
`τ = .arrow τ₁ τ₂`) that its arm establishes — and that is what keeps this combinator inside the
generic totality story. Were the proofs passed, `gu`/`ga`'s *types* would mention `τ`, so the
`match τ with` in `total_Ty_caseTy`'s witness would generalize them too, leaving `(hu ⋯).val` inside
a matcher arm where `hu` is the arm's own binder and nothing can project it. Escaping that costs a
named `TGen.caseTy` twin whose match is generator code by construction: a hand-written failure-free
twin, per datatype, that no registry validates.

Non-dependent, the split moves inside `TGen.mk` exactly the way `X.total_cases` does it, and no twin
is needed. The equations are not lost, only relocated: `support_Ty_caseTy` states them as
conjuncts. -/
def caseTy
    (τ : Ty)
    (gu : PGen α)
    (ga : Ty → Ty → PGen α) :
    PGen α :=
  match τ with
  | .unit => gu
  | .arrow τ₁ τ₂ => ga τ₁ τ₂

@[simp]
theorem support_arbTy :
    support arbTy = fun _ => True := by
  simp only [arbTy, TGen.arbTy, Ty.toGen_unfold]
  generalize (0 : Nat) = d
  simp only [TGen.toGen_frequency, TGen.toGen_pure, List.map_cons, List.map_nil, Ty.support_unfold]
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
  simp only [arbTy, TGen.arbTy, Ty.toGen_unfold]
  generalize (0 : Nat) = d
  simp only [TGen.toGen_frequency, TGen.toGen_pure, List.map_cons, List.map_nil,
    Ty.someSupport_unfold]
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

/-- Each arm contributes its branch's support, guarded by the equation that arm establishes. -/
@[simp]
theorem support_Ty_caseTy
    {gu : PGen α}
    {ga : Ty → Ty → PGen α} :
    support (caseTy τ gu ga) =
    (fun a =>
      (τ = Ty.unit ∧ a ∈ 〚gu〛) ∨
      (∃ (τ₁ τ₂ : Ty), τ = Ty.arrow τ₁ τ₂ ∧ a ∈ 〚ga τ₁ τ₂〛)) := by
  funext
  apply propext
  cases τ <;> simp [caseTy]

@[gen_congr]
theorem support_caseTy_congr
    {unitCase unitCase' : PGen α}
    {arrowCase arrowCase' : Ty → Ty → PGen α}
    {h_unitCase : support unitCase = support unitCase'}
    {h_arrowCase : ∀ {τ₁ τ₂}, support (arrowCase τ₁ τ₂) = support (arrowCase' τ₁ τ₂)} :
    support (caseTy τ unitCase arrowCase) = support (caseTy τ unitCase' arrowCase') := by
  cases τ <;> simp [caseTy, h_unitCase, h_arrowCase]

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
        gu.val
        (fun τ₁ τ₂ => (ga τ₁ τ₂).val)) <| by
    match τ with
    | .unit => simp [gu.property, h]
    | .arrow τ₁ τ₂ => simp [(ga τ₁ τ₂).property, h, caseTy]

end CorrectGen

namespace Total

/-- Direct `⟨witness, proof⟩` with the `unfold arbTy` confined to the proof — `arbTy` is
`@[irreducible]`, so the goal has to be opened, and the only question is where.

Opened by `simp only` in tactic mode the whole witness ends up under an `Eq.mpr`, and an `Eq.mpr` in
the **data** path stops `.val` from projecting; `genWellScoped` then prints this one node as a
150-line `Eq.mpr … ⟨…, congrFun' (congrFun' (congrArg …))⟩` congruence tree in a term whose whole
purpose is to be read and pasted. With `arbTy` defined as a coercion, the data is the failure-free
generator itself and the proof is `rfl` under the unfold.

Same shape as `total_arbLabel`, which is `@[irreducible]` for the same reason. -/
@[total]
def total_arbTy : total arbTy := ⟨TGen.arbTy, by unfold arbTy; rfl⟩

/-- The witness is a `match` on `τ` producing `TGen`s — mirroring `caseTy`'s own match — placed
**inside** `TGen.mk`, and **not** `by cases τ`.

`total` is `Type`-valued, so `cases` in tactic mode is `Ty.rec` *in the data path*. The projection
`.val` then has nothing to reduce, and the generator reaches the environment as a recursor
application, which the code generator rejects with "does not support recursor `Ty.rec`". Moving the
`mk` outermost lets `.run` cancel at the top and leaves the `match` where it belongs, in the
generator's body. `genWellTyped` is the only generator that reaches this rule, so nothing else in
the corpus exercises it.

This is the same discipline `Total.lean` states for the generic combinators and `X.total_cases` for
the base functor: direct `⟨data, proof⟩`, with tactics confined to the proof. It is available here
only because `caseTy`'s branches are non-dependent; see its docstring. -/
@[total]
def total_Ty_caseTy
    {gu : PGen α}
    {ga : Ty → Ty → PGen α}
    (hu : total gu)
    (ha : ∀ τ₁ τ₂, total (ga τ₁ τ₂)) :
    total (PGen.caseTy τ gu ga) :=
  ⟨⟨fun {_G} _ => match τ with
                  | .unit => hu.val.run
                  | .arrow τ₁ τ₂ => (ha τ₁ τ₂).val.run⟩,
   by cases τ
      · exact hu.property
      · exact (ha _ _).property⟩

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
