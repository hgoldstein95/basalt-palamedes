import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace SortedBetweenFold

def isSortedBetweenFold (lo hi : Nat) (xs : List Nat) : Prop :=
  List.fold (fun _ => true) (fun x b s => decide (s ≤ x) && decide (x ≤ hi) && b x) xs lo

def genSortedBetweenFold (lo hi : Nat) : PGen (List Nat) := by
  generator_search (fun xs => isSortedBetweenFold lo hi xs = true)

end SortedBetweenFold
