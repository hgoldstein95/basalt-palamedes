/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: `= 2 ∨ = 5`

Synthesizes `genEq2Or5 : G Nat` for `fun a => a = 2 ∨ a = 5`, a disjunctive predicate over two
literal values.
-/

open Palamedes

def genEq2Or5 [Gen G] : G Nat := by
  generator_search (fun a => a = 2 ∨ a = 5)
