import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace NonemptyFold

def isNonemptyFold (t : Palamedes.Tree α) : Bool :=
  Palamedes.Tree.fold false (fun _ _ _ => true) t

def genNonemptyFold : Gen (Palamedes.Tree Nat) := by
  generator_search (fun t => isNonemptyFold t = true)

end NonemptyFold
