import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace CompleteFold

@[simp]
def isCompleteFold (t : Palamedes.Tree Nat) (n : Nat) : Bool :=
  Palamedes.Tree.fold (fun s => s == 0) (fun bl _ br s => decide (s > 0) && bl (s - 1) && br (s - 1)) t n

def genCompleteFold (n : Nat) : Gen (Palamedes.Tree Nat) := by
  generator_search (fun t => isCompleteFold t n = true)

end CompleteFold
