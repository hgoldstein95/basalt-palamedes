import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace TrueAccuOpt

@[simp]
def isTrueAccuOpt (xs : List α) : Option Unit :=
  List.accuM
      (fun _ _ => ())
      (fun _ => some ())
      (fun _ _ _ => guard true)
      xs
      ()

def genTrueAccuOpt : PGen (List Nat) := by
  generator_search (fun xs => isTrueAccuOpt xs = some ())

end TrueAccuOpt
