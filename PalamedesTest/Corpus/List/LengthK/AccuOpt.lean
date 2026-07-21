import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace LengthKAccuOpt

@[simp]
def lengthAccuOpt (xs : List α) : Option Nat :=
  List.accuM
    (fun _ _ => ())
    (fun _ => some 0)
    (fun _ b _ => some (b + 1))
    xs
    ()

def genLengthKAccuOpt {k : Nat} : PGen (List Nat) := by
  generator_search (fun xs => lengthAccuOpt xs = some k)

end LengthKAccuOpt
