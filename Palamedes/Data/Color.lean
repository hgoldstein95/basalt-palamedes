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
import Palamedes.SomeSupport

/-!
# `Color` primitives

The two-constructor `Color` type (red/black, for red-black trees), `arbColor`, its
support/totality facts, the synthesis rules `s_arbColor` and `s_caseColor`, and a `ToString`
instance.
-/

section TypeDef

inductive Color where
  | red
  | black
deriving DecidableEq, Repr

@[simp]
theorem Color.exists_color {P : Color → Prop} : (∃ c, P c) ↔ P .red ∨ P .black := by
  apply Iff.intro <;> intro h
  . let ⟨c, h⟩ := h
    cases c <;> aesop
  . cases h <;> aesop

end TypeDef

namespace Palamedes

open Palamedes.PGen

namespace PGen

def arbColor : PGen Color := pick (pure .red) (pure .black)

@[simp]
theorem support_arbColor :
    support arbColor = fun _ => True := by
    funext x; cases x <;> simp_all [arbColor]

@[simp]
theorem someSupport_arbColor : someSupport arbColor = fun _ => True := by
  funext x; cases x <;> simp_all [arbColor]

namespace CorrectGen

@[extract, aesop safe apply (rule_sets := [synthesis])]
def s_arbColor : @CorrectGen Color (fun _ => True) :=
  Subtype.mk arbColor <| by
    funext v
    simp

@[extract, case_split]
def s_caseColor
    {Q : α → Prop}
    {P : α → Color → Prop}
    (c: Color)
    (h : ∀ {a}, P a c = Q a)
    (gr : CorrectGen (fun a => P a .red))
    (gb : CorrectGen (fun a => P a .black)) :
    CorrectGen Q :=
  Subtype.mk (if c = .red then gr.val else gb.val) <| by
    match c with
    | .red => simp [gr.property, h]
    | .black => simp [gb.property, h]

end CorrectGen

namespace Total

@[total]
def total_arbColor : total (arbColor : PGen Color) :=
  total_pick (total_pure _) (total_pure _)

/-- Same hazard as `total_Bool_rec`; see there. -/
@[total]
def total_Color_rec (hr : total gr) (hb : total gb) : total (Color.rec gr gb c) :=
  ⟨⟨fun {_G} _ => match c with | .red => hr.val.run | .black => hb.val.run⟩, by
    cases c
    · exact hr.property
    · exact hb.property⟩

end Total

end PGen

end Palamedes

namespace PrettyPrint

def Color.toString : Color → String
  | .red => "red"
  | .black => "black"

instance : ToString Color where
  toString := Color.toString

end PrettyPrint
