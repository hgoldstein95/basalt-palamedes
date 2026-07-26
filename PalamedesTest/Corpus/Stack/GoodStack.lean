/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: stacks of good atoms

Synthesizes `genGoodStack : G Stack` from `isGoodStack`, which holds when every atom in a
length-`n` stack passes `isGoodAtom`/`isGoodNat` (the 3-constructor `Stack` datatype). Pins the
emitted term under `#guard_msgs`.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace GoodStack

@[simp]
def isGoodNat (n : Nat) : Bool :=
  n == 0 || n == 1

@[simp]
def isGoodAtom : Atom → Bool
  | .atm n _ => isGoodNat n

@[simp]
def isGoodStack (s : Stack) (n : Nat) : Bool :=
  match s with
  | .mty => n == 0
  | .cons x s' => (n > 0 && isGoodAtom x) && isGoodStack s' (n - 1)
  | .ret_cons pc s' => (n > 0 && isGoodAtom pc) && isGoodStack s' (n - 1)

/--
info: Try this:
  [apply] exact
    Stack.unfoldGo
      (fun d x => do
        let a ←
          if x.2 = 0 then pure StackF.mty
            else
              _root_.frequency
                [(1, fun x => do
                    let a ←
                      _root_.frequency
                          [(1, fun x => do
                              let a ← RandomChoice.pick (fun x => pure Label.low) fun x => pure Label.high
                              pure (Atom.atm 0 a)),
                            (1, fun x => do
                              let a ← RandomChoice.pick (fun x => pure Label.low) fun x => pure Label.high
                              pure (Atom.atm 1 a))]
                    pure (StackF.cons a PUnit.unit)),
                  (1, fun x => do
                    let a ←
                      _root_.frequency
                          [(1, fun x => do
                              let a ← RandomChoice.pick (fun x => pure Label.low) fun x => pure Label.high
                              pure (Atom.atm 0 a)),
                            (1, fun x => do
                              let a ← RandomChoice.pick (fun x => pure Label.low) fun x => pure Label.high
                              pure (Atom.atm 1 a))]
                    pure (StackF.ret_cons a PUnit.unit))]
        match a with
          | StackF.mty => pure StackF.mty
          | StackF.cons a1 a2 => pure (StackF.cons a1 (a2, x.2 - 1))
          | StackF.ret_cons a1 a2 => pure (StackF.ret_cons a1 (a2, x.2 - 1)))
      0 (PUnit.unit, n)
-/
#guard_msgs in
def genGoodStack (n : Nat) [Gen G] : G Stack := by
  generator_search? (fun s => isGoodStack s n = true)

end GoodStack
