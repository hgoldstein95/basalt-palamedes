import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

def genSmall : Gen Nat := by
  generator_search (fun a => a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4)
