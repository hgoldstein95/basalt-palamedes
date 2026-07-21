/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace NonemptyFold

def isNonemptyFold (t : Palamedes.Tree α) : Bool :=
  Palamedes.Tree.fold false (fun _ _ _ => true) t

def genNonemptyFold : PGen (Palamedes.Tree Nat) := by
  generator_search (fun t => isNonemptyFold t = true)

end NonemptyFold
