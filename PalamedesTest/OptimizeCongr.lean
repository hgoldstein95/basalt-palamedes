/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Support

/-!
# `@[gen_congr]` registration guards

The optimizer's descent selects one rule per head and keeps the first match, so both a malformed
statement and a second rule for a claimed head are rejected when the lemma is tagged.
-/

open Palamedes Palamedes.PGen

/--
error: `@[gen_congr]`: `PalamedesTest.notCongr` is not a support-congruence lemma of the form `support (H …) = support (H …)` with at least one differing argument
-/
#guard_msgs in
@[gen_congr] theorem PalamedesTest.notCongr : (1 : Nat) = 1 := rfl

/--
error: `@[gen_congr]`: `PalamedesTest.shadowsPickCongr` and `Palamedes.support_pick_congr` both descend through `Palamedes.PGen.pick`, so the optimizer would have to choose between them. Keep one.
-/
#guard_msgs in
@[gen_congr] theorem PalamedesTest.shadowsPickCongr
    {x x' y y' : PGen α}
    (hx : support x = support x')
    (hy : support y = support y') :
    support (pick x y) = support (pick x' y') :=
  support_pick_congr hx hy
