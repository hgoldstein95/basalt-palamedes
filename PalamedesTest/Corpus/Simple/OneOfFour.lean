/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: one of four literals

Synthesizes `genSmall : G Nat` for `fun a => a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4`. Pins the emitted
term: the optimizer's flatten pass turns the search's `pick` tree into a uniform four-way choice, so
every branch carries weight `1` (a surviving `pick` chain would show ½, ¼, ⅛, ⅛). At the Basalt
shape that prints as Basalt's own `frequency`; `PalamedesTest/Stats.lean` pins the distribution it
actually produces.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

/--
info: Try this:
  [apply] exact
    _root_.frequency [(1, fun x => pure 1), (1, fun x => pure 2), (1, fun x => pure 3), (1, fun x => pure 4)]
-/
#guard_msgs in
def genSmall [Gen G] : G Nat := by
  generator_search? (fun a => a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4)
