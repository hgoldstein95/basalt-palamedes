import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace LengthK

def genLengthK {k : Nat} : PGen (List Nat) := by
  generator_search (fun xs => List.length xs = k)

end LengthK
