import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

/--
info: Try this:
  [apply] exact pure 2
-/
#guard_msgs in
def genEq2 : PGen Nat := by
  generator_search? (· = 2)
