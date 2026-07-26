/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: length k (accuM/Option)

Synthesizes `genLengthKAccuOpt : G (List Nat)` for `lengthAccuOpt`, the length predicate
spelled via the accumulating `List.accuM`/`Option` fold path.
-/

open Palamedes

namespace LengthKAccuOpt

@[simp]
def lengthAccuOpt (xs : List α) : Option Nat :=
  List.accuM
    (fun _ _ => ())
    (fun _ => some 0)
    (fun _ b _ => some (b + 1))
    xs
    ()

def genLengthKAccuOpt {k : Nat} [Gen G] : G (List Nat) := by
  generator_search (fun xs => lengthAccuOpt xs = some k)

end LengthKAccuOpt
