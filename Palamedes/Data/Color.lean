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
import Palamedes.Derive.Enum

/-!
# `Color` primitives

The two-constructor `Color` type (red/black, for red-black trees), its derived draw layer, the
case-split rule `s_caseColor`, and a `ToString` instance.
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

derive_enum_gen Color

namespace Palamedes

open Palamedes.PGen

namespace PGen

namespace CorrectGen

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

end PGen

end Palamedes

namespace PrettyPrint

def Color.toString : Color → String
  | .red => "red"
  | .black => "black"

instance : ToString Color where
  toString := Color.toString

end PrettyPrint
