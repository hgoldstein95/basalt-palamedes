/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: well-scoped STLC terms

Synthesizes `genWellScoped : PGen Term` from `isWellScoped`, which holds when every `var` index is
below the ambient binder count; exercises the `dite` distribution (`var`/`app` under the `unit`
leaf's scope check). Pins the emitted term under `#guard_msgs`.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace WellScoped

@[simp]
def isWellScoped (t : Term) (varCap : Nat) : Bool :=
  match t with
  | .unit => true
  | .var n => n < varCap
  | .abs _ t => isWellScoped t (varCap + 1)
  | .app t₁ t₂ => isWellScoped t₁ varCap && isWellScoped t₂ varCap

/--
info: Try this:
  [apply] exact
    Term.unfold
      (fun d p => do
        let tv ←
          if h : decide (p.2 > 0) = true then
              PGen.oneOf
                [pure TermF.unit, do
                  let a ← lt p.2 (s_lt_partial._proof_1 h)
                  pure (TermF.var a), do
                  let a ← arbTy
                  pure (TermF.abs a PUnit.unit), pure (TermF.app PUnit.unit PUnit.unit)]
            else
              PGen.oneOf
                [pure TermF.unit, do
                  let a ← arbTy
                  pure (TermF.abs a PUnit.unit), pure (TermF.app PUnit.unit PUnit.unit)]
        match tv with
          | TermF.unit => pure TermF.unit
          | TermF.var a1 => pure (TermF.var a1)
          | TermF.abs a1 a2 => pure (TermF.abs a1 (a2, p.2 + 1))
          | TermF.app a1 a2 => pure (TermF.app (a1, p.2) (a2, p.2)))
      (PUnit.unit, 0)
-/
#guard_msgs in
def genWellScoped : PGen Term := by
  generator_search? (fun t => isWellScoped t 0 = true)

end WellScoped
