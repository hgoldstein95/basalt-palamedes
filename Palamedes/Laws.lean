/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Total
import Palamedes.SomeSupport

/-!
# Proving Basalt Laws for Palamedes Generators

The synthesizer proves `Palamedes.PGen.support g = P`, which implies (but is not identical to)
Basalt's `IsSoundAndComplete` (or this module's own `IsSomeSoundAndComplete` for partial
generators). This module bridges that gap.
-/

namespace Palamedes

open Palamedes.PGen

variable {α : Type} {P : α → Prop}

/-- The law for a generator emitted at `G α`, from the totality witness. -/
theorem isSoundAndComplete_of_total {t : TGen α} {g : PGen α}
    (hw : t.toGen = g) (h : g.support = P) :
    IsSoundAndComplete (t.run (G := SPMF)) P := by
  subst hw
  intro a
  exact iff_of_eq (congrFun h a)

/-- Soundness and completeness for a filtering generator: the values it actually produces are
exactly `P`.

NOTE: This is not defined in Basalt, although in principle it could (and maybe should) be. -/
def IsSomeSoundAndComplete (g : SPMF (Option α)) (P : α → Prop) : Prop :=
  ∀ a, some a ∈ SPMF.support g ↔ P a

/-- The law for a generator emitted on the filtering path. -/
theorem isSomeSoundAndComplete_of_someSupport {g : PGen α} (h : someSupport g = P) :
    IsSomeSoundAndComplete (PGen.totalize g (G := SPMF)) P :=
  fun a => iff_of_eq (congrFun h a)

end Palamedes
