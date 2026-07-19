import Palamedes.Synthesizer
import Palamedes.Sample

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace RBTFold

@[simp]
def isRRFold (t : Palamedes.Tree (Color × α)) : Bool :=
  Palamedes.Tree.fold
    (fun _ => true)
    (fun bl c br isRedChild => if c.fst == .red then !isRedChild && bl true && br true else bl false && br false)
    t
    false

@[simp]
def isBHFold (t : Palamedes.Tree (Color × α)) (height : Nat) : Bool :=
  Palamedes.Tree.fold
    (fun h => h == 0)
    (fun bl c br h => if c.fst == .red then bl h && br h else h >= 0 && bl (h - 1) && br (h - 1))
    t
    height

@[simp]
def isBSTFold (t : Palamedes.Tree (α × Nat)) : Nat × Nat -> Bool := fun (lo, hi) =>
  Palamedes.Tree.fold
        (fun _ => true)
        (fun bl x br s =>
          match s with
          | (sl, sr) => (decide (sl ≤ x.snd) && decide (x.snd ≤ sr)) && bl (sl, x.snd - 1) && br (x.snd + 1, sr))
        t (lo, hi)

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

@[simp]
def isRBTFold (height lo hi : Nat) (t : Palamedes.Tree (Color × Nat)) : Bool :=
  isBHFold t height = true ∧ isRRFold t = true ∧ isBSTFold t (lo, hi) = true

def genRBTFold (height lo hi : Nat) [_root_.Gen G] :
    G (Option (Palamedes.Tree (Color × Nat))) := by
  generator_search (fun t => isRBTFold lo hi height t = true)

end RBTFold
