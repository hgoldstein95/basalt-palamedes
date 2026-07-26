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
# `Bool` primitives

`arbBool`, its support/`someSupport`/totality facts, and the synthesis rules `s_arbBool` and
`s_caseBool`.
-/

namespace Palamedes

open Palamedes.PGen

namespace PGen

def arbBool : PGen Bool := pick (pure true) (pure false)

@[simp]
theorem support_arbBool :
    support arbBool = fun _ => True := by
    funext x; cases x <;> simp_all [arbBool]

/-- The `someSupport` twin, for the filtering path's law. Same script: `arbBool` is a `pick` of two
`pure`s, and the combinator twins cover both. -/
@[simp]
theorem someSupport_arbBool : someSupport arbBool = fun _ => True := by
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

@[total]
def total_arbBool : total (arbBool : PGen Bool) :=
  total_pick (total_pure _) (total_pure _)

/-- The case split stays **inside** `TGen.mk`, for the reason `total_dite` and `X.total_cases` give:
`by cases b <;> assumption` puts `Bool.rec` in the data path, where `.val` cannot project past it
until `b` is concrete, and the Basalt shape then emits `(Bool.rec … b).val.run` instead of a
generator. A `match` rather than `Bool.rec` in the data — the conclusion is keyed on `Bool.rec`
because that is what the descent dispatches on, but the code generator rejects a bare recursor. -/
@[total]
def total_Bool_rec (hf : total gf) (ht : total gt) : total (Bool.rec gf gt b) :=
  ⟨⟨fun {_G} _ => match b with | false => hf.val.run | true => ht.val.run⟩, by
    cases b
    · exact hf.property
    · exact ht.property⟩

end Total

end PGen

end Palamedes
