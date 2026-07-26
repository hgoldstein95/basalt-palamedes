/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: well-scoped STLC terms

Synthesizes `genWellScoped : G Term` from `isWellScoped`, which holds when every `var` index is
below the ambient binder count; exercises the `dite` distribution (`var`/`app` under the `unit`
leaf's scope check). Pins the emitted term under `#guard_msgs`.
-/

open Palamedes

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
    Term.unfoldGo
      (fun d x => do
        let a ←
          if h : decide (x.2 > 0) = true then
              frequency
                [(1, fun x => pure TermF.unit),
                  (1, fun x_1 => do
                    let a ← (TGen.choose 0 (x.2 - 1) (PGen.lt._proof_1 x.2)).run
                    pure (TermF.var a)),
                  (1, fun x => do
                    let a ← TGen.arbTy.run
                    pure (TermF.abs a PUnit.unit)),
                  (1, fun x => pure (TermF.app PUnit.unit PUnit.unit))]
            else
              frequency
                [(1, fun x => pure TermF.unit),
                  (1, fun x => do
                    let a ← TGen.arbTy.run
                    pure (TermF.abs a PUnit.unit)),
                  (1, fun x => pure (TermF.app PUnit.unit PUnit.unit))]
        match a with
          | TermF.unit => pure TermF.unit
          | TermF.var a1 => pure (TermF.var a1)
          | TermF.abs a1 a2 => pure (TermF.abs a1 (a2, x.2 + 1))
          | TermF.app a1 a2 => pure (TermF.app (a1, x.2) (a2, x.2)))
      0 (PUnit.unit, 0)
-/
#guard_msgs in
def genWellScoped [Gen G] : G Term := by
  generator_search? (fun t => isWellScoped t 0 = true)

end WellScoped
