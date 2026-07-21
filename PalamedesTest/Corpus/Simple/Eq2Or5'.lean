import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

def genEq2Or5' : PGen Nat := by
  generator_search (fun a => a = 2 ∨ a = 5 ∧ True)
