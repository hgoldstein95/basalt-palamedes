import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace IncreasingByOneTree

@[simp]
def isIncreasingByOneAux (t : Palamedes.Tree Nat) (prev : Nat) : Bool :=
  match t with
  | .leaf => true
  | .node l x r => x == prev + 1 && isIncreasingByOneAux l x && isIncreasingByOneAux r x

@[simp]
def isIncreasingByOne (t : Palamedes.Tree Nat) : Bool :=
  isIncreasingByOneAux t 0

def genIncreasingByOne : Gen (Palamedes.Tree Nat) := by
  generator_search (fun t => isIncreasingByOne t = true)

end IncreasingByOneTree
