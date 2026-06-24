import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

def genFstIsTwo : Gen (Nat × Nat) := by
  generator_search (fun p => p.fst = 2)

def genFixedPair : Gen (Nat × Nat) := by
  generator_search (fun p => p.1 = 2 ∧ p.2 = 3)

def genSuccPair : Gen (Nat × Nat) := by
  generator_search (fun p => p.1 = 2 ∧ p.2 = p.1 + 1)

def genDiagonal : Gen (Nat × Nat) := by
  generator_search (fun p => p.1 = p.2)

def genOffByOne : Gen (Nat × Nat) := by
  generator_search (fun p => ∃ a, p.1 = a ∧ p.2 = a + 1)
