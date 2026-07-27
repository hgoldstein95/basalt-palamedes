/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer
import Palamedes.Tuning

/-!
# Corpus: Well-Typed STLC Terms

This example requires `Tuning` for a.s. termination.
-/

open Palamedes

namespace WellTyped

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
/--
info: Try this:
  [apply] exact do
    let a ← TGen.arbTy.run
    Term.unfoldGo
        (fun d x => do
          let a ←
            match x.1 with
              | Ty.unit =>
                if h : decide (List.length (List.idxsOf Ty.unit x.2) > 0) = true then
                  frequency
                    [(Tuning.weight θ 0 d, fun x => pure TermF.unit),
                      (Tuning.weight θ 1 d, fun x_1 => do
                        let a ← (TGen.elements (List.idxsOf Ty.unit x.2)).run
                        pure (TermF.var a)),
                      (Tuning.weight θ 2 d, fun x => do
                        let a ← TGen.arbTy.run
                        pure (TermF.app (Ty.arrow a Ty.unit) a))]
                else
                  frequency
                    [(Tuning.weight θ 3 d, fun x => pure TermF.unit),
                      (Tuning.weight θ 4 d, fun x => do
                        let a ← TGen.arbTy.run
                        pure (TermF.app (Ty.arrow a Ty.unit) a))]
              | Ty.arrow τ₁ τ₂ =>
                if h : decide (List.length (List.idxsOf (Ty.arrow τ₁ τ₂) x.2) > 0) = true then
                  frequency
                    [(Tuning.weight θ 5 d, fun x_1 => do
                        let a ← (TGen.elements (List.idxsOf (Ty.arrow τ₁ τ₂) x.2)).run
                        pure (TermF.var a)),
                      (Tuning.weight θ 6 d, fun x => pure (TermF.abs τ₁ τ₂)),
                      (Tuning.weight θ 7 d, fun x => do
                        let a ← TGen.arbTy.run
                        pure (TermF.app (Ty.arrow a (Ty.arrow τ₁ τ₂)) a))]
                else
                  frequency
                    [(Tuning.weight θ 8 d, fun x => pure (TermF.abs τ₁ τ₂)),
                      (Tuning.weight θ 9 d, fun x => do
                        let a ← TGen.arbTy.run
                        pure (TermF.app (Ty.arrow a (Ty.arrow τ₁ τ₂)) a))]
          match a with
            | TermF.unit => pure TermF.unit
            | TermF.var a1 => pure (TermF.var a1)
            | TermF.abs a1 a2 => pure (TermF.abs a1 (a2, a1 :: x.2))
            | TermF.app a1 a2 => pure (TermF.app (a1, x.2) (a2, x.2)))
        0 (a, Γ)
-/
#guard_msgs in
def genWellTyped (Γ : List Ty) (θ : Tuning) [Gen G] : G Term := by
  generator_search? (fun t => isWellTyped Γ t)

/-!
To run the above generator, we recommend the following tuning, which has been designed to ensure
that the generator terminates
```lean
genWellTyped Γ (SchedulePolicy.stlc.materialize genWellTyped.sites)
```
Future versions of Palamedes will derive a tuning like this automatically.
-/

/--
info: def Palamedes.SchedulePolicy.stlc : SchedulePolicy :=
{
  weight := fun x =>
    match x with
    | 0 => { base := 1, growth := 30 }
    | 1 => { base := 1, growth := 14 }
    | x => { base := 4, growth := 0 } }
-/
#guard_msgs in
#print SchedulePolicy.stlc

end WellTyped
