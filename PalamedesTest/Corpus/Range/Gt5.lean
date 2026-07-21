import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

def genGt5 : PGen Nat := by
  generator_search fun n => n > 5
