import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

/--
info: Try this:
  [apply] exact pure 2
-/
#guard_msgs in
def genEq2 : Gen Nat := by
  generator_search? (· = 2)
