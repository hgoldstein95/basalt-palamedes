/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: `2 = ·`

Synthesizes `genEq2' : PGen Nat` for the predicate with the equality flipped (`2 = ·` instead of
`· = 2`), checking the search handles either orientation.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

def genEq2' : PGen Nat := by
  generator_search (2 = ·)
