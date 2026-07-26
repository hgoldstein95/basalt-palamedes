/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: unbounded range

Synthesizes `genGt5 : G Nat` for `fun n => n > 5`, a one-sided range with no upper bound.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

def genGt5 [Gen G] : G Nat := by
  generator_search fun n => n > 5
