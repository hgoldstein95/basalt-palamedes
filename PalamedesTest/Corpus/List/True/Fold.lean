/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: vacuous list predicate (fold)

Synthesizes `genTrueFold : G (List Nat)` for `isTrueFold`, the fold-spelled twin of `isTrue` via
`List.fold`, exercising a different search path than the structurally recursive sibling.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace TrueFold

@[simp]
def isTrueFold (xs : List α) : Bool :=
  List.fold true (fun _ b => b) xs

def genTrueFold [Gen G] : G (List Nat) := by
  generator_search (fun xs => isTrueFold xs = true)

end TrueFold
