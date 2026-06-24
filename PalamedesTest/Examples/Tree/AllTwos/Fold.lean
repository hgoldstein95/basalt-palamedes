import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace AllTwosTreeFold

@[simp]
def isAllTwosFold (t : Palamedes.Tree Nat) : Bool :=
  Palamedes.Tree.fold (fun bl x br => x == 2 && bl && br) true t

def genAllTwosFold : Gen (Palamedes.Tree Nat) := by
  generator_search (fun t => isAllTwosFold t = true)

end AllTwosTreeFold
