import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace IncreasingByOneListFold

def isIncreasingByOneFold (xs : List Nat) : Bool :=
  List.fold (fun _ => true) (fun x b prev => x == prev + 1 && b x) xs 0

def genIncreasingByOneFold : PGen (List Nat) := by
  generator_search (fun xs => isIncreasingByOneFold xs = true)

end IncreasingByOneListFold
