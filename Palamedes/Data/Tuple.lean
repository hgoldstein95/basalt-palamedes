import Palamedes.Total
import Palamedes.CorrectGen
import Palamedes.Optimizer
import Palamedes.RuleSets

namespace Palamedes

open Gen

namespace Gen

namespace CorrectGen

def s_arbTuple
    {P : α × β → Prop}
    (g : CorrectGen (fun (p : α × β) => ∃ (a : α) (b : β), P (a, b) ∧ p = (a, b))) :
    CorrectGen (fun (p : α × β) => P p) :=
  Subtype.mk g.val <| by
    funext (a, b)
    simp_all [g.property]

@[extract]
theorem s_arbTuple_val
    {P : α × β → Prop}
    (g : CorrectGen (fun (p : α × β) => ∃ (a : α) (b : β), P (a, b) ∧ p = (a, b))) :
    (s_arbTuple g).val = g.val := rfl

end CorrectGen

end Gen

end Palamedes
