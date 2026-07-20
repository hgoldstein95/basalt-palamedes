import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

/--
info: Try this:
  [apply] exact Gen.oneOf [pure 1, pure 2, pure 3, pure 4]
-/
#guard_msgs in
def genSmall : Gen Nat := by
  generator_search? (fun a => a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4)
