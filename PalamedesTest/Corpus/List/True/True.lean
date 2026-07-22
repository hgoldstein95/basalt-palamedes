/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: vacuous list predicate (structural)

Synthesizes `genTrue : PGen (List Nat)` for `isTrue`, a predicate that holds of every list.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace ConstTrue

@[simp]
def isTrue : List α → Bool
  | [] => true
  | x :: xs => (fun _ => true) x && isTrue xs

def genTrue : PGen (List Nat) := by
  generator_search (fun xs => isTrue xs = true)

end ConstTrue
