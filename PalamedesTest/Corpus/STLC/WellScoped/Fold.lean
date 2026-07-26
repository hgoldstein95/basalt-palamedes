/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: well-scoped STLC terms, fold-spelled

Synthesizes `genWellScopedFold : G Term` from `isWellScopedFold`, the fold-spelled twin of
`isWellScoped`.
-/

open Palamedes

namespace WellScopedFold

@[simp]
def isWellScopedFold (t : Term) (varCap : Nat)  : Bool :=
  Term.fold (fun _ => true) (fun n s => s < n) (fun _ b s => b (s + 1)) (fun b₁ b₂ s => b₁ s && b₂ s) t varCap

def genWellScopedFold [Gen G] : G Term := by
  generator_search (fun t => isWellScopedFold t 0 = true)

end WellScopedFold
