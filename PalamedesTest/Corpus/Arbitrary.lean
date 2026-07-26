/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: unconstrained values

Synthesizes `genUnit`, `genBool`, and `genNat` for the vacuous predicate `fun _ => True` at three
different carrier types.
-/

open Palamedes

def genUnit [Gen G] : G Unit := by
  generator_search (fun (_ : Unit) => True)

def genBool [Gen G] : G Bool := by
  generator_search (fun _ => True)

def genNat [Gen G] : G Nat := by
  generator_search (fun _ => True)
