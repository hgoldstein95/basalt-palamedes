import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace BST

@[simp]
def isBST : Palamedes.Tree Nat → (Nat × Nat) → Bool := fun t ⟨lo, hi⟩ =>
  match t with
  | .leaf => true
  | .node l x r =>
    (lo <= x && x <= hi) &&
    isBST l ⟨lo, x - 1⟩ &&
    isBST r ⟨x + 1, hi⟩

def genBST (lo hi : Nat) : Gen (Palamedes.Tree Nat) := by
  generator_search (fun t => isBST t (lo, hi) = true) with_policy

end BST
