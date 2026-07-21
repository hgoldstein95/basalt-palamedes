import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

def genZeroOrInRange (lo hi : Nat) : PGen Nat := by
  generator_search fun n => n = 0 ∨ (lo ≤ n ∧ n ≤ hi)
