/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: vacuous list predicate (accuM/Option)

Synthesizes `genTrueAccuOpt : G (List Nat)` for `isTrueAccuOpt`, the vacuous predicate spelled
via the accumulating `List.accuM`/`Option` fold path.
-/

open Palamedes

namespace TrueAccuOpt

@[simp]
def isTrueAccuOpt (xs : List α) : Option Unit :=
  List.accuM
      (fun _ _ => ())
      (fun _ => some ())
      (fun _ _ _ => guard true)
      xs
      ()

def genTrueAccuOpt [Gen G] : G (List Nat) := by
  generator_search (fun xs => isTrueAccuOpt xs = some ())

end TrueAccuOpt
