/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

set_option maxHeartbeats 1000000

namespace WellTypedFold

@[simp]
def getTypeFold (t : Term) (Γ : List Ty) : Option Ty :=
  Term.fold
    (fun _ => pure .unit)
    (fun n Γ' => Γ'[n]?)
    (fun τ₁ b Γ' => do
      let τ₂ ← b (τ₁ :: Γ')
      pure (.arrow τ₁ τ₂))
    (fun b₁ b₂ Γ' => do
      let τ₁ ← b₁ Γ'
      let τ₂ ← b₂ Γ'
      match τ₁ with
      | .arrow τarg τres => do
        guard (τarg == τ₂)
        pure τres
      | Ty.unit => failure) t Γ

@[simp]
def isWellTypedFold (Γ : List Ty) (t : Term) : Prop :=
  ∃ τ, getTypeFold t Γ = some τ

attribute [local simp] Ty.as_or Ty.deforest_eq in
def genWellTypedFold (Γ : List Ty) : PGen Term := by
  generator_search (fun t => isWellTypedFold Γ t)

end WellTypedFold
