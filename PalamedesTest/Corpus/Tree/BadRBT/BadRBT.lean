import Palamedes.Synthesizer
import Palamedes.Data.Color

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace BadRBT

@[simp]
def isRRAux : Palamedes.Tree (Color × α) → Bool → Bool := λ t isRedChild =>
 match t with
 | .leaf => true
 | .node l c r => if c.fst == .red then !isRedChild && isRRAux l true && isRRAux r true else isRRAux l false && isRRAux r false

@[simp]
def isRR : Palamedes.Tree (Color × α) → Bool := λ t => isRRAux t false

@[simp]
def isBH : Palamedes.Tree (Color × α) → Nat → Bool := λ t height =>
 match t with
 | .leaf => height == 0
 | .node l c r => if c.fst == .red then isBH l height && isBH r height else height >= 0 && isBH l (height - 1) && isBH r (height - 1)

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

@[simp]
def isBadRBT : Palamedes.Tree (Color × Nat) → Nat → Bool := λ t height =>
  isRR t = true ∧ isBH t height = true

def genBadRBT (height : Nat) : Gen (Palamedes.Tree (Color × Nat)) := by
  generator_search (fun t => isBadRBT t height)

end BadRBT
