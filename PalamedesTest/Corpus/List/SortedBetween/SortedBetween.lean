/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: sorted between lo and hi (structural)

Synthesizes `genSortedBetween lo hi : G (List Nat)` for `isSortedBetween`, a sorted-list
predicate that threads the running lower bound as state. Pins the emitted term under
`#guard_msgs`.
-/

open Palamedes

namespace SortedBetween

@[simp]
def isSortedBetween (xs : List Nat) : Nat × Nat → Bool := fun (lo, hi) =>
  match xs with
  | [] => true
  | x :: xs' => (lo <= x && x <= hi) && isSortedBetween xs' (x, hi)

/--
info: Try this:
  [apply] exact
    List.unfoldGo
      (fun d x => do
        let a ←
          if hb : decide (x.2.1 ≤ x.2.2) = true then
              frequency
                [(1, fun x => pure ListF.nil),
                  (1, fun x_1 => do
                    let a ← chooseNat x.2.1 x.2.2
                    pure (ListF.cons a PUnit.unit))]
            else pure ListF.nil
        match a with
          | ListF.nil => pure ListF.nil
          | ListF.cons a1 a2 => pure (ListF.cons a1 (a2, a1, x.2.2)))
      0 (PUnit.unit, lo, hi)
-/
#guard_msgs in
def genSortedBetween (lo hi : Nat) [Gen G] : G (List Nat) := by
  generator_search? (fun xs => isSortedBetween xs (lo, hi) = true)

end SortedBetween
