import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace MaxDepthFold

@[simp]
def isMaxDepthFold (t : Palamedes.Tree Nat) (n : Nat) : Bool :=
  Palamedes.Tree.fold (fun _ => true) (fun bl _ br s => decide (s > 0) && bl (s - 1) && br (s - 1)) t n

def genMaxDepthFold (n : Nat) : Gen (Palamedes.Tree Nat) := by
  generator_search (fun t => isMaxDepthFold t n = true)

end MaxDepthFold
