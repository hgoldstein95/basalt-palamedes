import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace AllTwosEvenLenFold

@[simp]
def isAllTwosEvenLenFold (xs : List Nat) : Bool :=
  List.fold true (fun x b => x == 2 && b) xs = true ∧ List.fold true (fun _ b => !b) xs

def genAllTwosEvenLenFold : Gen (List Nat) := by
  generator_search (fun xs => isAllTwosEvenLenFold xs = true)

end AllTwosEvenLenFold
