/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: even length (structural)

Synthesizes `genEvenLen : PGen (List Nat)` for `isEvenLen`, defined by structural recursion that
flips a boolean per element.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace EvenLen

@[simp]
def isEvenLen : List α → Bool
  | [] => true
  | _ :: xs => !(isEvenLen xs)

def genEvenLen : PGen (List Nat) := by
  generator_search (fun xs => isEvenLen xs = true)

end EvenLen
