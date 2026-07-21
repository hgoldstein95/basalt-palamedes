import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

def genUnit : PGen Unit := by
  generator_search (fun (_ : Unit) => True)

def genBool : PGen Bool := by
  generator_search (fun _ => True)

def genNat : PGen Nat := by
  generator_search (fun _ => True)
