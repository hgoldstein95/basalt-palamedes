import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

/--
info: Try this:
  [apply] exact pure 4
-/
#guard_msgs in
def genThreePlusOne : Gen Nat := by
  generator_search? (fun b => ∃ a, a = 3 ∧ b = a + 1)
