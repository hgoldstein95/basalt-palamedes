/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: `= 2`

Synthesizes `genEq2 : G Nat` for the trivial predicate `(· = 2)`. Pins the emitted term
(`pure 2`) under `#guard_msgs`.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

/--
info: Try this:
  [apply] exact pure 2
-/
#guard_msgs in
def genEq2 [Gen G] : G Nat := by
  generator_search? (· = 2)
