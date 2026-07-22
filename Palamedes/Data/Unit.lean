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

/-!
# `Unit` primitives

`arbUnit`, its synthesis rule `s_arbUnit`, and its totality fact.
-/

namespace Palamedes

open Palamedes.PGen

namespace PGen

@[reducible, extract]
def arbUnit : PGen Unit := pure ()

namespace CorrectGen

@[extract, aesop safe apply (rule_sets := [synthesis])]
def s_arbUnit : @CorrectGen Unit (fun _ => True) :=
  Subtype.mk arbUnit (by simp [arbUnit])

end CorrectGen

namespace Total

@[total]
def total_arbUnit : total arbUnit :=
  total_pure ()

end Total

end PGen

end Palamedes
