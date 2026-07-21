import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace AllTwosFold

@[simp]
def isAllTwosFold (xs : List Nat) : Bool :=
  List.fold true (fun x b => x == 2 && b) xs

def genAllTwosFold : PGen (List Nat) := by
  generator_search (fun xs => isAllTwosFold xs = true)

end AllTwosFold
