import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace AllTwosTree

@[simp]
def isAllTwos : Palamedes.Tree Nat → Bool
  | .leaf => true
  | .node l x r => x = 2 && isAllTwos l && isAllTwos r

def genAllTwos : Gen (Palamedes.Tree Nat) := by
  generator_search (fun t => isAllTwos t)

end AllTwosTree
