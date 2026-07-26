/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: pairs

Synthesizes `G (Nat × Nat)` generators for predicates over pairs: a fixed first component
(`genFstIsTwo`), both fixed (`genFixedPair`), one component depending on the other (`genSuccPair`,
`genOffByOne`), and equality of the two (`genDiagonal`). `genSuccPair` pins the emitted term under
`#guard_msgs`.
-/

open Palamedes

def genFstIsTwo [Gen G] : G (Nat × Nat) := by
  generator_search (fun p => p.fst = 2)

def genFixedPair [Gen G] : G (Nat × Nat) := by
  generator_search (fun p => p.1 = 2 ∧ p.2 = 3)

/--
info: Try this:
  [apply] exact pure (2, 3)
-/
#guard_msgs in
def genSuccPair [Gen G] : G (Nat × Nat) := by
  generator_search? (fun p => p.1 = 2 ∧ p.2 = p.1 + 1)

def genDiagonal [Gen G] : G (Nat × Nat) := by
  generator_search (fun p => p.1 = p.2)

def genOffByOne [Gen G] : G (Nat × Nat) := by
  generator_search (fun p => ∃ a, p.1 = a ∧ p.2 = a + 1)
