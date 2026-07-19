import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace Nonempty

@[simp]
def isNonempty : Palamedes.Tree α → Bool
  | .leaf => false
  | .node l _ r => true && isNonempty l && isNonempty r

def genNonempty : Gen (Palamedes.Tree Nat) := by
  generator_search (fun t => isNonempty t = true)

end Nonempty
