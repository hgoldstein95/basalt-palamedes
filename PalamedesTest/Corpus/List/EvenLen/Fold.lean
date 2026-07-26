/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: even length (fold)

Synthesizes `genEvenLenFold : G (List Nat)` for `isEvenLenFold`, the fold-spelled twin of
`isEvenLen` via `List.fold`, exercising a different search path than the structurally recursive
sibling.
-/

open Palamedes

namespace EvenLenFold

@[simp]
def isEvenLenFold (xs : List α) : Bool :=
  List.fold true (fun _ b => !b) xs

def genEvenLenFold [Gen G] : G (List Nat) := by
  generator_search (fun xs => isEvenLenFold xs = true)

end EvenLenFold
