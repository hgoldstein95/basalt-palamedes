import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace MaxDepth

@[simp]
def isMaxDepth (t : Palamedes.Tree α) (n : Nat) : Bool :=
  match t with
  | .leaf => true
  | .node l _ r =>
    n > 0 &&
    isMaxDepth l (n - 1) &&
    isMaxDepth r (n - 1)

def genComplete (n : Nat) : Gen (Palamedes.Tree Nat) := by
  generator_search (fun t => isMaxDepth t n = true)

end MaxDepth
