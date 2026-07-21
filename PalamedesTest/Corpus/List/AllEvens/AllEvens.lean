import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace AllEvens

@[simp]
def isAllEvens : List Nat → Bool
  | [] => true
  | x :: xs => x % 2 = 0 && isAllEvens xs

def genAllEvens : PGen (List Nat) := by
  generator_search (fun xs => isAllEvens xs)

end AllEvens
