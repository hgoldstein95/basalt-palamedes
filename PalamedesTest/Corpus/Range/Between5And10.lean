/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: fixed range

Synthesizes `genBetween5And10 : G Nat` for `fun n => 5 ≤ n ∧ n ≤ 10`, a range with literal
bounds.
-/

open Palamedes

def genBetween5And10 [Gen G] : G Nat := by
  generator_search (fun n => 5 ≤ n ∧ n ≤ 10)
