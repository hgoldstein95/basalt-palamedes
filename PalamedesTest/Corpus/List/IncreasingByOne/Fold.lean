/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: increasing by one (fold)

Synthesizes `genIncreasingByOneFold : PGen (List Nat)` for `isIncreasingByOneFold`, the
fold-spelled twin of `isIncreasingByOne` via `List.fold`, exercising a different search path than
the structurally recursive sibling.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace IncreasingByOneListFold

def isIncreasingByOneFold (xs : List Nat) : Bool :=
  List.fold (fun _ => true) (fun x b prev => x == prev + 1 && b x) xs 0

def genIncreasingByOneFold : PGen (List Nat) := by
  generator_search (fun xs => isIncreasingByOneFold xs = true)

end IncreasingByOneListFold
