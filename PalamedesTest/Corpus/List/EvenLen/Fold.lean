/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace EvenLenFold

@[simp]
def isEvenLenFold (xs : List α) : Bool :=
  List.fold true (fun _ b => !b) xs

def genEvenLenFold : PGen (List Nat) := by
  generator_search (fun xs => isEvenLenFold xs = true)

end EvenLenFold
