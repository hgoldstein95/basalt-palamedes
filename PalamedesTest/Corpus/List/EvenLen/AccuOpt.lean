/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: even length (accuM/Option)

Synthesizes `genEvenLenAccuOpt : G (List Nat)` for `isEvenLenAccuOpt`, spelled via
`List.accuM`/`Option` fusion rather than structural recursion or `List.fold`. Pins the emitted term
under `#guard_msgs`.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace EvenLenAccuOpt

@[simp]
def isEvenLenAccuOpt (xs : List α) : Option Bool :=
  List.accuM
      (fun _ _ => ())
      (fun _ => some true)
      (fun _ b _ => some (!b))
      xs
      ()

/--
info: Try this:
  [apply] exact
    List.unfoldGo
      (fun d x => do
        let a ←
          if hb : x.1 = true then
              _root_.frequency
                [(1, fun x => pure ListF.nil),
                  (1, fun x => do
                    let a ← TGen.arbNat.run
                    pure (ListF.cons a false))]
            else do
              let a ← TGen.arbNat.run
              pure (ListF.cons a true)
        match a with
          | ListF.nil => pure ListF.nil
          | ListF.cons a1 a2 => pure (ListF.cons a1 (a2, PUnit.unit)))
      0 (true, PUnit.unit)
-/
#guard_msgs in
def genEvenLenAccuOpt [Gen G] : G (List Nat) := by
  generator_search? (fun xs => isEvenLenAccuOpt xs = some true)

end EvenLenAccuOpt
