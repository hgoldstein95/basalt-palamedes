/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: length k and all-twos (structural)

Synthesizes `genLengthKAllTwos k : PGen (List Nat)` for `isLengthKAllTwos`, the conjunction of a
fixed length and `isAllTwos`.
-/

set_option maxHeartbeats 1000000

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace LengthKAllTwos

@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

@[simp]
def isLengthKAllTwos (k : Nat) (xs : List Nat) : Bool :=
  xs.length == k && isAllTwos xs

@[simp]
def genLengthKAllTwos (k : Nat) : PGen (List Nat) := by
  generator_search (fun xs => isLengthKAllTwos k xs = true)

end LengthKAllTwos
