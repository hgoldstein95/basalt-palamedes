/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer
import Palamedes.Tuning

/-!
# Corpus: well-typed STLC terms

Synthesizes `genWellTyped : G Term` from `isWellTyped`, the existential well-typedness
predicate over `getType`; a growing-seed generator, so a `Tuning` binder and a decaying schedule are
required for a.s. termination. Runs near a raised `maxHeartbeats`; distribution pinned by
`Optimizer/Schedule.lean`.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace WellTyped

set_option maxHeartbeats 5000000

@[simp]
def getType (t : Term) (Γ : List Ty) : Option Ty :=
  match t with
  | .unit => pure .unit
  | .var n => Γ[n]?
  | .abs τ t => do
    let τ' ← getType t (τ :: Γ)
    pure (.arrow τ τ')
  | .app t₁ t₂ => do
    let τ₁ ← getType t₁ Γ
    let τ₂ ← getType t₂ Γ
    match τ₁ with
    | .arrow τarg τres => do
      guard (τarg == τ₂)
      pure τres
    | .unit => failure

@[simp]
def isWellTyped (Γ : List Ty) (t : Term) : Prop :=
  ∃ (τ : Ty), getType t Γ = τ

attribute [local simp] Ty.as_or Ty.deforest_eq in
/-- The well-typed-term generator: `app` invents its argument type and recurses on `σ → τ` for a
freshly generated `σ`, so the seed *grows*. At the default `.uniform` weighting it is supercritical
and diverges when sampled directly; the usable generator is
`genWellTyped Γ (SchedulePolicy.stlc.materialize genWellTyped.sites)`, whose depth-decaying weights
force closure. The `θ` binder is what makes that call possible — without one the generator would
ship uniform and there would be nothing to weight. -/
def genWellTyped (Γ : List Ty) (θ : Tuning := .uniform) [Gen G] : G Term := by
  generator_search (fun t => isWellTyped Γ t)

end WellTyped
