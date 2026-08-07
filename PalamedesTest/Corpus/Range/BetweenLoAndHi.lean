/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: symbolic range (filtering)

Synthesizes `genBetweenLoAndHi lo hi : G (Option Nat)` for `fun n => lo ≤ n ∧ n ≤ hi` with symbolic
bounds, a filtering generator. Pins the emitted term under `#guard_msgs`.

The pin is where the *filtering* shape's emission is legible: the generator is read at `OptionT G`,
so the rejecting branch is an ordinary `pure none` draw and nothing names `Palamedes.PGen`. A
carrier combinator reappearing here means the push stopped early — `PalamedesTest/Extract.lean`
fails the build on that too, but this says which generator and what it stopped at.
-/

open Palamedes

/--
info: Try this:
  [apply] exact if h : decide (lo ≤ hi) = true then chooseNat lo hi else pure none
-/
#guard_msgs in
def genBetweenLoAndHi (lo hi : Nat) [Gen G] : G (Option Nat) := by
  generator_search? (fun n => lo ≤ n ∧ n ≤ hi)

/-! ## The pinned text re-elaborates

A `#guard_msgs` pin checks what the term *printed as*, not that the printed text means anything, and
the two come apart exactly where a delaborator drops an argument it should have kept. Declaring the
pin a second time as an ordinary `def` is what closes that gap.

`Corpus/List/IdxOf/` does the same for the total shape. Both are needed: the shapes are emitted by
different passes and print different vocabulary — a witness projected to `TGen.run` there, the
guard's `dite` and a dropped `chooseNat` side condition here. -/

def genBetweenLoAndHiPasted (lo hi : Nat) [Gen G] : G (Option Nat) :=
  if h : decide (lo ≤ hi) = true then chooseNat lo hi else pure none
