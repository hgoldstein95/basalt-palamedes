/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: all-twos and even length (fold)

Synthesizes `genAllTwosEvenLenFold : G (List Nat)` for `isAllTwosEvenLenFold`, the fold-spelled
twin of `isAllTwosEvenLen` via `List.fold`, exercising a different search path than the
structurally recursive sibling.
-/

open Palamedes

namespace AllTwosEvenLenFold

@[simp]
def isAllTwosEvenLenFold (xs : List Nat) : Bool :=
  List.fold true (fun x b => x == 2 && b) xs = true ∧ List.fold true (fun _ b => !b) xs

def genAllTwosEvenLenFold [Gen G] : G (List Nat) := by
  generator_search (fun xs => isAllTwosEvenLenFold xs = true)

end AllTwosEvenLenFold
