import Palamedes.Total
import Palamedes.CorrectGen
import Palamedes.Optimizer
import Palamedes.RuleSets

namespace Palamedes

open Palamedes.PGen

namespace PGen

namespace CorrectGen

@[extract, aesop 50% apply (rule_sets := [synthesis])]
def s_arbTuple
    {P : α × β → Prop}
    (g : CorrectGen (fun (p : α × β) => ∃ (a : α) (b : β), P (a, b) ∧ p = (a, b))) :
    CorrectGen (fun (p : α × β) => P p) :=
  Subtype.mk g.val <| by
    funext (a, b)
    simp_all [g.property]

end CorrectGen

end PGen

end Palamedes
