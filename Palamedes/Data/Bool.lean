import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Total
import Palamedes.RuleSets
import Palamedes.CaseSplit

namespace Palamedes

open Gen

namespace Gen

def arbBool : Gen Bool := pick (pure true) (pure false)

@[simp]
theorem support_arbBool :
    support arbBool = fun _ => True := by
    funext x; cases x <;> simp_all [arbBool]

namespace CorrectGen

@[extract, aesop safe apply (rule_sets := [synthesis])]
def s_arbBool : @CorrectGen Bool (fun _ => True) :=
  Subtype.mk arbBool (by simp [arbBool])

@[extract, case_split]
def s_caseBool
    {Q : α → Prop}
    {P : α → Bool → Prop}
    (b : Bool)
    (h : ∀ {a}, P a b = Q a)
    (gt : CorrectGen (fun a => P a true))
    (gf : CorrectGen (fun a => P a false)) :
    CorrectGen Q :=
  Subtype.mk (if h : b then gt.val else gf.val) <| by
    match b with
    | true => simp [gt.property, h]
    | false => simp [gf.property, h]

end CorrectGen

namespace Total

@[simp, total]
theorem total_arbBool : total (arbBool : Gen Bool) := by
  simp [arbBool]

@[simp, total]
theorem total_Bool_rec (hf : total gf) (ht : total gt) : total (Bool.rec gf gt b) := by
  cases b <;> simp_all

end Total

end Gen

end Palamedes
