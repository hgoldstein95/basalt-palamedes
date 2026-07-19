import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Total
import Palamedes.RuleSets
import Palamedes.CaseSplit
import Palamedes.Data.Nat

section TypeDef
/- adapted from https://github.com/QuickChick/QuickChick/tree/master/examples/ifc-basic -/

inductive Label where
  | low
  | high
deriving DecidableEq

inductive Atom where
  | atm (n : Nat) (l : Label)

end TypeDef

namespace Palamedes

open _root_.Palamedes.Gen

namespace Gen

@[irreducible]
def arbLabel  : Gen Label :=
  pick (pure .low) (pure .high)

@[simp]
theorem support_arbLabel : support arbLabel = fun _ => True := by
  funext v
  cases v <;> simp_all [arbLabel]

namespace CorrectGen

@[extract, aesop safe apply (rule_sets := [synthesis])]
def s_arbLabel : @CorrectGen Label (fun _ => True) :=
  Subtype.mk arbLabel <| by
    funext v
    simp

@[extract, case_split]
def s_caseLabel
    {Q : α → Prop}
    {P : α → Label → Prop}
    (l : Label)
    (h : ∀ {a}, P a l = Q a)
    (gl : CorrectGen (fun a => P a .low))
    (gh : CorrectGen (fun a => P a .high)) :
    CorrectGen Q :=
  Subtype.mk (if l = .low then gl.val else gh.val) <| by
    match l with
    | .low => simp [gl.property, h]
    | .high => simp [gh.property, h]

@[extract]
def s_arbAtom
    {P : Atom → Prop}
    (g : CorrectGen (fun (a : Atom) => ∃ (n : Nat) (l : Label), P (.atm n l) ∧ a = .atm n l)) :
    CorrectGen (fun (a : Atom) => P a) :=
  Subtype.mk g.val <| by
    funext (.atm n l)
    simp_all [g.property]

end CorrectGen

namespace Total

@[simp, total]
theorem total_arbLabel : total arbLabel := by
  simp [arbLabel]

end Total

end Gen

end Palamedes

namespace PrettyPrint

def Label.toString : Label → String
  | .low => "low"
  | .high => "high"

instance : ToString Label where
  toString := Label.toString

def Atom.toString : Atom → String
  | .atm n l => s!"({n} {l})"

instance : ToString Atom where
  toString := Atom.toString

end PrettyPrint
