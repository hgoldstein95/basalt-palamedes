import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

def genThreePlusOne : Gen Nat := by
  generator_search (fun b => ∃ a, a = 3 ∧ b = a + 1)
