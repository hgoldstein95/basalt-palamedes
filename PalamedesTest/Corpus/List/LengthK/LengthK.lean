/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: length k (structural)

Synthesizes `genLengthK : G (List Nat)` for `List.length xs = k`, a symbolic target length.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace LengthK

def genLengthK {k : Nat} [Gen G] : G (List Nat) := by
  generator_search (fun xs => List.length xs = k)

end LengthK
