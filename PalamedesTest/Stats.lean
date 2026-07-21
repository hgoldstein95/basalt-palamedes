import Palamedes.Stats
import PalamedesTest.Corpus.Simple.OneOfFour
import PalamedesTest.Corpus.Tree.BST.Fold

open Palamedes Palamedes.PGen

/--
info: (toStatGen genSmall) — 1000 draws (seed 0, fuel 10000)

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
#genstats (toStatGen genSmall)

/--
info: (toStatGen (choose 0 10 (by omega))) — 1000 draws (seed 0, fuel 10000)

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
#genstats (toStatGen (choose 0 10 (by omega)))

/--
info: (toStatGen (BSTFold.genBSTFold 0 10)) — 4000 draws (seed 0, fuel 10000)

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
#genstats (draws := 4000) (toStatGen (BSTFold.genBSTFold 0 10))
