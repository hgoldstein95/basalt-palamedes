import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace AllTwosFold

@[simp]
def isAllTwosFold (xs : List Nat) : Bool :=
  List.fold true (fun x b => x == 2 && b) xs

def genAllTwosFold : Gen (List Nat) := by
  generator_search (fun xs => isAllTwosFold xs = true)

end AllTwosFold
