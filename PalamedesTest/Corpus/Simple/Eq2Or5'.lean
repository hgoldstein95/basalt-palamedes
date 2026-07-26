/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: `= 2 ∨ (= 5 ∧ True)`

Synthesizes `genEq2Or5' : G Nat` for `fun a => a = 2 ∨ a = 5 ∧ True`, checking the search sees
through a redundant `∧ True` conjunct.
-/

open Palamedes

def genEq2Or5' [Gen G] : G Nat := by
  generator_search (fun a => a = 2 ∨ a = 5 ∧ True)
