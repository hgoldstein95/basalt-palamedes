import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

def genGt5 : Gen Nat := by
  generator_search fun n => n > 5
