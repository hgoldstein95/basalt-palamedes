/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Data.Nat
import PalamedesTest.Corpus.Simple.OneOfFour
import PalamedesTest.Corpus.Tree.BST.Fold
import PalamedesTest.Corpus.Tree.RBT.RBT
import PalamedesTest.Corpus.Tree.BadRBT.BadRBT

/-!
# Distribution oracles for `#genstats`

Pins `#genstats` reports under `#guard_msgs`: that the flatten pass yields a *uniform* choice
(`genSmall` at ~25% per branch — a `pick` tree would show ½, ¼, ⅛, ⅛), `choose`'s uniform range,
and a shrinking-seed recursive generator (`genBSTFold`).

`#genstats` is Basalt's own command and every generator here is Basalt-shaped, so nothing in this
file adapts anything. The range draw reaches it as Basalt's own `chooseNat`, which is what a
synthesized generator emits for a range and is already `[Gen G] → G Nat` — there is no carrier to
project and no `Fail` instance required.
-/

open Palamedes

/--
info: genSmall — 1000 draws (seed 0, fuel 10000)

  outcomes    ok 1000 (100.0%)
  size        mean 3.5   p50 3   p95 5   max 5
  choices     mean 1.0   p50 1   p95 1   max 1
  distinct    4 / 1000

  head constructor
    succ   100.0%  (1000)

  most common
     25.9%  (259)  1
     25.4%  (254)  2
     24.4%  (244)  3
     24.3%  (243)  4

  samples
    2
    3
    1
-/
#guard_msgs in
#genstats genSmall

/--
info: (chooseNat 0 10) — 1000 draws (seed 0, fuel 10000)

  outcomes    ok 1000 (100.0%)
  size        mean 6.1   p50 6   p95 11   max 11
  choices     mean 1.0   p50 1   p95 1   max 1
  distinct    11 / 1000

  head constructor
    succ    90.7%  (907)
    zero     9.3%   (93)

  most common
      9.8%  (98)  7
      9.7%  (97)  9
      9.6%  (96)  4
      9.3%  (93)  0
      9.3%  (93)  3

  samples
    8
    3
    9
-/
#guard_msgs in
#genstats (chooseNat 0 10)

/--
info: (BSTFold.genBSTFold 0 10) — 4000 draws (seed 0, fuel 10000)

  outcomes    ok 4000 (100.0%)
  size        mean 4.2   p50 3   p95 13   max 31
  choices     mean 4.9   p50 3   p95 16   max 33
  distinct    963 / 4000

  head constructor
    node    50.4%  (2015)
    leaf    49.6%  (1985)

  most common
     49.6%  (1985)  Palamedes.Tree.leaf
      2.1%    (84)  Palamedes.Tree.node (Palamedes.Tree.leaf) 10 (Palamedes.Tree.leaf)
      1.5%    (59)  Palamedes.Tree.node (Palamedes.Tree.leaf) 8 (Palamedes.Tree.leaf)
      1.4%    (57)  Palamedes.Tree.node (Palamedes.Tree.leaf) 3 (Palamedes.Tree.leaf)
      1.3%    (51)  Palamedes.Tree.node (Palamedes.Tree.leaf) 2 (Palamedes.Tree.leaf)

  samples
    Palamedes.Tree.node (Palamedes.Tree.leaf) 10 (Palamedes.Tree.leaf)
    Palamedes.Tree.leaf
    Palamedes.Tree.leaf
-/
#guard_msgs in
#genstats (draws := 4000) (BSTFold.genBSTFold 0 10)

/--
info: (RBT.genRBT 1 0 10) — 200 draws (seed 0, fuel 10000)

  outcomes    ok 200 (100.0%)
  size        mean 1.0   p50 1   p95 1   max 1
  choices     mean 13.9   p50 13   p95 25   max 35
  distinct    180 / 200

  head constructor
    some    94.5%  (189)
    none     5.5%   (11)

  most common
      5.5%  (11)  none
      2.0%   (4)  some (Palamedes.Tree.node (Palamedes.Tree.leaf) (Color.black, 3) (Palamedes.Tree.leaf))
      1.5%   (3)  some (Palamedes.Tree.node (Palamedes.Tree.leaf) (Color.black, 8) (Palamedes.Tree.leaf))
      1.5%   (3)  some (Palamedes.Tree.node (Palamedes.Tree.leaf) (Color.black, 9) (Palamedes.Tree.node (Pa…
      1.0%   (2)  some (Palamedes.Tree.node (Palamedes.Tree.leaf) (Color.black, 1) (Palamedes.Tree.leaf))

  samples
    some (Palamedes.Tree.node (Palamedes.Tree.node (Palamedes.Tree.leaf) (Color.red, 0) (Pala…
    none
    some (Palamedes.Tree.node (Palamedes.Tree.node (Palamedes.Tree.node (Palamedes.Tree.leaf)…
-/
#guard_msgs in
#genstats (draws := 200) (RBT.genRBT 1 0 10)

/--
info: (BadRBT.genBadRBT 1) — 200 draws (seed 0, fuel 10000)

  outcomes    ok 55 (27.5%)   fuel-exhausted 145 (72.5%)
  size        mean 17.6   p50 11   p95 53   max 75
  choices     mean 33.9   p50 22   p95 107   max 158
  distinct    44 / 55

  head constructor
    node   100.0%  (55)

  most common
     12.7%  (7)  Palamedes.Tree.node (Palamedes.Tree.leaf) (Color.black, 0) (Palamedes.Tree.leaf)
      5.5%  (3)  Palamedes.Tree.node (Palamedes.Tree.leaf) (Color.black, 1) (Palamedes.Tree.node (Palamede…
      5.5%  (3)  Palamedes.Tree.node (Palamedes.Tree.leaf) (Color.black, 2) (Palamedes.Tree.leaf)
      3.6%  (2)  Palamedes.Tree.node (Palamedes.Tree.leaf) (Color.black, 1) (Palamedes.Tree.leaf)

  samples
    Palamedes.Tree.node (Palamedes.Tree.node (Palamedes.Tree.node (Palamedes.Tree.leaf) (Colo…
    Palamedes.Tree.node (Palamedes.Tree.leaf) (Color.black, 3) (Palamedes.Tree.node (Palamede…
    Palamedes.Tree.node (Palamedes.Tree.leaf) (Color.black, 0) (Palamedes.Tree.leaf)
-/
#guard_msgs in
#genstats (draws := 200) (BadRBT.genBadRBT 1)
