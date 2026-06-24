import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

def genEq2 : Gen Nat := by
  generator_search (· = 2)
