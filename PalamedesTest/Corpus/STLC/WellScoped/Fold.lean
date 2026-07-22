/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: well-scoped STLC terms, fold-spelled

Synthesizes `genWellScopedFold : PGen Term` from `isWellScopedFold`, the fold-spelled twin of
`isWellScoped`.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace WellScopedFold

@[simp]
def isWellScopedFold (t : Term) (varCap : Nat)  : Bool :=
  Term.fold (fun _ => true) (fun n s => s < n) (fun _ b s => b (s + 1)) (fun b₁ b₂ s => b₁ s && b₂ s) t varCap

def genWellScopedFold : PGen Term := by
  generator_search (fun t => isWellScopedFold t 0 = true)

end WellScopedFold
