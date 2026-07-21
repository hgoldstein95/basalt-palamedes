import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace WellScopedFold

@[simp]
def isWellScopedFold (t : Term) (varCap : Nat)  : Bool :=
  Term.fold (fun _ => true) (fun n s => s < n) (fun _ b s => b (s + 1)) (fun b₁ b₂ s => b₁ s && b₂ s) t varCap

def genWellScopedFold : PGen Term := by
  generator_search (fun t => isWellScopedFold t 0 = true)

end WellScopedFold
