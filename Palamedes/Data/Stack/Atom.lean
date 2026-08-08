/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.PGen
import Palamedes.CorrectGen
import Palamedes.Total
import Palamedes.RuleSets
import Palamedes.CaseSplit
import Palamedes.Data.Nat

/-!
# `Label` and `Atom` primitives

The IFC stack machine's atoms (adapted from QuickChick's ifc-basic example): `arbLabel`, its
support/totality facts, and the synthesis rules `s_arbLabel`, `s_caseLabel`, and `s_arbAtom`.
-/

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

open Palamedes.PGen

/-! ## The primitive

A label draw cannot fail, so it is spelled at the failure-free interface `TGen` and its `PGen` form
is `TGen.toGen` of it; see the section header in `Data/Nat.lean` for why the twin belongs in
`Palamedes.TGen` and not `Palamedes.PGen.TGen`. -/

namespace TGen

/-- An arbitrary security label, uniform over the two. -/
def arbLabel : TGen Label := TGen.pick (TGen.pure .low) (TGen.pure .high)

end TGen

namespace PGen

/-- `@[irreducible]` so the optimizer treats a label draw as an opaque primitive rather than
descending into it and flattening the `pick` into the enclosing choice. -/
@[irreducible]
def arbLabel : PGen Label := TGen.arbLabel.toGen

@[simp]
theorem support_arbLabel : support arbLabel = fun _ => True := by
  funext v
  cases v <;> simp_all [arbLabel, TGen.arbLabel]

@[simp]
theorem someSupport_arbLabel : someSupport arbLabel = fun _ => True := by
  funext v
  cases v <;> simp_all [arbLabel, TGen.arbLabel]

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

/-- The `unfold` is confined to the proof component: written `by unfold arbLabel; exact …` instead,
the whole term sits under an `Eq.mpr` in the **data** path, `.val` stops projecting, and the witness
reaches the environment as a proof term. Keeping the data a bare `TGen.arbLabel` is also what makes
`genGoodStack` print each of its four label draws as one named generator instead of an inlined
`pick`. -/
@[total]
def total_arbLabel : total arbLabel := ⟨TGen.arbLabel, by unfold arbLabel; rfl⟩

/-- Same hazard as `total_Bool_rec`; see there. -/
@[total]
def total_Label_rec (hl : total gl) (hh : total gh) : total (Label.rec gl gh l) :=
  ⟨⟨fun {_G} _ => match l with | .low => hl.val.run | .high => hh.val.run⟩, by
    cases l
    · exact hl.property
    · exact hh.property⟩

end Total

end PGen

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
