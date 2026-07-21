import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace IncreasingByOneTreeFold

@[simp]
def isIncreasingByOneFold (t : Palamedes.Tree Nat) : Bool :=
  Palamedes.Tree.fold (fun _ => true) (fun bl x br prev => x == prev + 1 && bl x && br x) t 0

def genIncreasingByOneFold : PGen (Palamedes.Tree Nat) := by
  generator_search (fun t => isIncreasingByOneFold t = true)

end IncreasingByOneTreeFold
