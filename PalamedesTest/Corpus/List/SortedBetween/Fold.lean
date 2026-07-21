/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace SortedBetweenFold

def isSortedBetweenFold (lo hi : Nat) (xs : List Nat) : Prop :=
  List.fold (fun _ => true) (fun x b s => decide (s ≤ x) && decide (x ≤ hi) && b x) xs lo

def genSortedBetweenFold (lo hi : Nat) : PGen (List Nat) := by
  generator_search (fun xs => isSortedBetweenFold lo hi xs = true)

end SortedBetweenFold
