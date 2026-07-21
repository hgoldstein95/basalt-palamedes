import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace AllEvensFold

@[simp]
def isAllEvensFold (xs : List Nat) : Bool :=
  List.fold true (fun x b => x % 2 == 0 && b) xs

def genAllEvensFold : PGen (List Nat) := by
  generator_search (fun xs => isAllEvensFold xs = true)

end AllEvensFold
