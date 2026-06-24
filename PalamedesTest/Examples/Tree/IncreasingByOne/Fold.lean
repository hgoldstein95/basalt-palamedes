import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace IncreasingByOneTreeFold

@[simp]
def isIncreasingByOneFold (t : Palamedes.Tree Nat) : Bool :=
  Palamedes.Tree.fold (fun bl x br prev => x == prev + 1 && bl x && br x) (fun _ => true) t 0

def genIncreasingByOneFold : Gen (Palamedes.Tree Nat) := by
  generator_search (fun t => isIncreasingByOneFold t = true)

end IncreasingByOneTreeFold
