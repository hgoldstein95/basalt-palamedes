import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace LengthKFold

@[simp]
def lengthFold (xs : List α) : Nat :=
  List.fold 0 (fun _ b => b + 1) xs

def genLengthKFold {k : Nat} : PGen (List Nat) := by
  generator_search (fun xs => lengthFold xs = k)

end LengthKFold
