import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace EvenLen

@[simp]
def isEvenLen : List α → Bool
  | [] => true
  | _ :: xs => !(isEvenLen xs)

def genEvenLen : PGen (List Nat) := by
  generator_search (fun xs => isEvenLen xs = true)

end EvenLen
