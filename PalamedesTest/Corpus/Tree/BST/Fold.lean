import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace BSTFold

@[simp]
def isBSTFold (lo hi : Nat) (t : Palamedes.Tree Nat) : Bool :=
  Palamedes.Tree.fold
        (fun _ => true)
        (fun bl x br s =>
          match s with
          | (sl, sr) => (decide (sl ≤ x) && decide (x ≤ sr)) && bl (sl, x - 1) && br (x + 1, sr))
        t (lo, hi)

def genBSTFold (lo hi : Nat) : PGen (Palamedes.Tree Nat) := by
  generator_search (fun t  => isBSTFold lo hi t = true)

end BSTFold
