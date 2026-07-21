import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

def genEq2' : PGen Nat := by
  generator_search (2 = ·)
