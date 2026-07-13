import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace EvenLenFold

@[simp]
def isEvenLenFold (xs : List α) : Bool :=
  List.fold true (fun _ b => !b) xs

def genEvenLenFold : Gen (List Nat) := by
  generator_search (fun xs => isEvenLenFold xs = true)

end EvenLenFold
