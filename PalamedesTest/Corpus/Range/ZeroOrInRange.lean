/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: zero or in range

Synthesizes `genZeroOrInRange lo hi : G Nat` for `fun n => n = 0 ∨ (lo ≤ n ∧ n ≤ hi)`, a
disjunction of a literal and a symbolic range.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

def genZeroOrInRange (lo hi : Nat) [Gen G] : G Nat := by
  generator_search fun n => n = 0 ∨ (lo ≤ n ∧ n ≤ hi)
