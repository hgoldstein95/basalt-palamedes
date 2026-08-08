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
# `Bool` primitives

The derived draw layer for `Bool` (`arbBool`, its support/`someSupport`/totality facts, and the
synthesis rule `s_arbBool`), plus the case-split rule `s_caseBool`.
-/

derive_enum_gen Bool

namespace Palamedes

open Palamedes.PGen

namespace PGen

namespace CorrectGen

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

end PGen

end Palamedes
