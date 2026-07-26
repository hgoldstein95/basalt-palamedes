/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: all-twos and even length (structural)

Synthesizes `genAllTwosEvenLen : G (List Nat)` for `isAllTwosEvenLen`, the conjunction of
`isAllTwos` and `isEvenLen`, each defined by structural recursion.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace AllTwosEvenLen

@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

@[simp]
def isEvenLen : List α → Bool
  | [] => true
  | _ :: xs => !(isEvenLen xs)

@[simp]
def isAllTwosEvenLen (xs : List Nat) : Bool :=
  isAllTwos xs && isEvenLen xs

def genAllTwosEvenLen [Gen G] : G (List Nat) := by
  generator_search (fun xs => isAllTwosEvenLen xs = true)

end AllTwosEvenLen
