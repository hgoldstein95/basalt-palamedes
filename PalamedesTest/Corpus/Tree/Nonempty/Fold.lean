/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: non-empty trees, fold-spelled

Synthesizes `genNonemptyFold : G (Palamedes.Tree Nat)` from `isNonemptyFold`, the fold-spelled
twin of `isNonempty`.
-/

open Palamedes

namespace NonemptyFold

def isNonemptyFold (t : Palamedes.Tree α) : Bool :=
  Palamedes.Tree.fold false (fun _ _ _ => true) t

def genNonemptyFold [Gen G] : G (Palamedes.Tree Nat) := by
  generator_search (fun t => isNonemptyFold t = true)

end NonemptyFold
