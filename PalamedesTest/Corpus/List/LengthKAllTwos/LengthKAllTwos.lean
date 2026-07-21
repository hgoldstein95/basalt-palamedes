import Palamedes.Synthesizer

set_option maxHeartbeats 1000000

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace LengthKAllTwos

@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

@[simp]
def isLengthKAllTwos (k : Nat) (xs : List Nat) : Bool :=
  xs.length == k && isAllTwos xs

@[simp]
def genLengthKAllTwos (k : Nat) : PGen (List Nat) := by
  generator_search (fun xs => isLengthKAllTwos k xs = true)

end LengthKAllTwos
