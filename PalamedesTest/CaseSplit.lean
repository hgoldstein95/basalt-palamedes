/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Data

/-!
# `@[case_split]` registration guards
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

/--
error: @[case_split]: PalamedesTest.notCorrectGen concludes in ℕ, not in `CorrectGen _`, so the case-split rule could never apply it
-/
#guard_msgs in
@[case_split] def PalamedesTest.notCorrectGen (_b : Bool) : Nat := 0

/--
error: @[case_split]: PalamedesTest.shadowsCaseBool and Palamedes.PGen.CorrectGen.s_caseBool both case-split on Bool, so the case-split rule would have to choose between them. Keep one, or give them distinct scrutinee types.
-/
#guard_msgs in
@[case_split] def PalamedesTest.shadowsCaseBool
    {Q : α → Prop}
    {P : α → Bool → Prop}
    (b : Bool)
    (h : ∀ {a}, P a b = Q a)
    (gt : CorrectGen (fun a => P a true))
    (gf : CorrectGen (fun a => P a false)) :
    CorrectGen Q :=
  s_caseBool b h gt gf
