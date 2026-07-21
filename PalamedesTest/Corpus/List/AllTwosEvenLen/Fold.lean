import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace AllTwosEvenLenFold

@[simp]
def isAllTwosEvenLenFold (xs : List Nat) : Bool :=
  List.fold true (fun x b => x == 2 && b) xs = true ∧ List.fold true (fun _ b => !b) xs

def genAllTwosEvenLenFold : PGen (List Nat) := by
  generator_search (fun xs => isAllTwosEvenLenFold xs = true)

end AllTwosEvenLenFold
