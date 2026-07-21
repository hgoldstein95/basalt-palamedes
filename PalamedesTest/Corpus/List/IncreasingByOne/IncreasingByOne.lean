/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace IncreasingByOneList

@[simp]
def isIncreasingByOneAux (xs : List Nat) (prev : Nat) : Bool :=
  match xs with
  | [] => true
  | x :: xs' => x == prev + 1 && isIncreasingByOneAux xs' x

@[simp]
def isIncreasingByOne (xs : List Nat) : Bool :=
  isIncreasingByOneAux xs 0

def genIncreasingByOneRec : PGen (List Nat) := by
  generator_search (fun xs => isIncreasingByOne xs = true)

end IncreasingByOneList
