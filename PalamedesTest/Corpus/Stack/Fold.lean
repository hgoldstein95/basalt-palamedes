/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace GoodStackFold

@[simp]
def isGoodNat (n : Nat) : Bool :=
  n == 0 || n == 1

@[simp]
def isGoodAtom : Atom → Bool
  | .atm n _ => isGoodNat n

def isGoodStackFold (s : Stack) (n : Nat) : Bool :=
  Stack.fold (fun i => i == 0) (fun x acc i => isGoodAtom x && acc (i - 1)) (fun pc acc i => isGoodAtom pc && acc (i - 1)) s n

def genGoodStackFold (n : Nat) : PGen Stack := by
  generator_search (fun s => isGoodStackFold s n = true)

end GoodStackFold
