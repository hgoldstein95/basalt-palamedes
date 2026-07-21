/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

def genUnit : PGen Unit := by
  generator_search (fun (_ : Unit) => True)

def genBool : PGen Bool := by
  generator_search (fun _ => True)

def genNat : PGen Nat := by
  generator_search (fun _ => True)
