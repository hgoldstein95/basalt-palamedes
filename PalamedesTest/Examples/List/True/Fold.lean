import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace TrueFold

@[simp]
def isTrueFold (xs : List α) : Bool :=
  List.fold true (fun _ b => b) xs

def genTrueFold : Gen (List Nat) := by
  generator_search (fun xs => isTrueFold xs = true)

end TrueFold
