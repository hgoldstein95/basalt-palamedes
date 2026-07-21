import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

def genBetween5And10 : PGen Nat := by
  generator_search (fun n => 5 ≤ n ∧ n ≤ 10)
