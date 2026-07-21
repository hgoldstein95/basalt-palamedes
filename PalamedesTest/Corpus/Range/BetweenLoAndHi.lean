import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

/--
info: Try this:
  [apply] exact totalize (assume (decide (lo ≤ hi)) fun h => choose lo hi)
-/
#guard_msgs in
def genBetweenLoAndHi (lo hi : Nat) [Gen G] : G (Option Nat) := by
  generator_search? (fun n => lo ≤ n ∧ n ≤ hi)
