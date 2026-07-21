/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

def genFstIsTwo : PGen (Nat × Nat) := by
  generator_search (fun p => p.fst = 2)

def genFixedPair : PGen (Nat × Nat) := by
  generator_search (fun p => p.1 = 2 ∧ p.2 = 3)

/--
info: Try this:
  [apply] exact pure (2, 3)
-/
#guard_msgs in
def genSuccPair : PGen (Nat × Nat) := by
  generator_search? (fun p => p.1 = 2 ∧ p.2 = p.1 + 1)

def genDiagonal : PGen (Nat × Nat) := by
  generator_search (fun p => p.1 = p.2)

def genOffByOne : PGen (Nat × Nat) := by
  generator_search (fun p => ∃ a, p.1 = a ∧ p.2 = a + 1)
