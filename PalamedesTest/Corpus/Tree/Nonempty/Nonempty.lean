/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace Nonempty

@[simp]
def isNonempty : Palamedes.Tree α → Bool
  | .leaf => false
  | .node l _ r => true && isNonempty l && isNonempty r

def genNonempty : PGen (Palamedes.Tree Nat) := by
  generator_search (fun t => isNonempty t = true)

end Nonempty
