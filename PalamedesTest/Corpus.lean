/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

/-
Aggregates the full example corpus. Compiling this module elaborates every example, each of which
synthesizes a generator at elaboration time and *fails to compile* if synthesis fails — so this
file is the de facto test suite. `PalamedesTest/Extract.lean` imports it to walk the corpus.
-/

import PalamedesTest.Corpus.Simple.Eq2
import PalamedesTest.Corpus.Simple.Eq2'
import PalamedesTest.Corpus.Simple.Eq2Or5
import PalamedesTest.Corpus.Simple.Eq2Or5'
import PalamedesTest.Corpus.Simple.OneOfFour
import PalamedesTest.Corpus.Simple.ThreePlusOne

import PalamedesTest.Corpus.Tuple.Pairs

import PalamedesTest.Corpus.Range.Between5And10
import PalamedesTest.Corpus.Range.BetweenLoAndHi
import PalamedesTest.Corpus.Range.Gt5
import PalamedesTest.Corpus.Range.ZeroOrInRange

import PalamedesTest.Corpus.Arbitrary

import PalamedesTest.Corpus.List.AllTwos.AllTwos
import PalamedesTest.Corpus.List.AllTwosEvenLen.AllTwosEvenLen
import PalamedesTest.Corpus.List.AllEvens.AllEvens
import PalamedesTest.Corpus.List.EvenLen.EvenLen
import PalamedesTest.Corpus.List.IncreasingByOne.IncreasingByOne
import PalamedesTest.Corpus.List.LengthK.LengthK
import PalamedesTest.Corpus.List.LengthKAllTwos.LengthKAllTwos
import PalamedesTest.Corpus.List.SortedBetween.SortedBetween
import PalamedesTest.Corpus.List.True.True

import PalamedesTest.Corpus.List.AllTwos.Fold
import PalamedesTest.Corpus.List.AllTwosEvenLen.Fold
import PalamedesTest.Corpus.List.AllEvens.Fold
import PalamedesTest.Corpus.List.EvenLen.Fold
import PalamedesTest.Corpus.List.IncreasingByOne.Fold
import PalamedesTest.Corpus.List.LengthK.Fold
import PalamedesTest.Corpus.List.LengthKAllTwos.Fold
import PalamedesTest.Corpus.List.SortedBetween.Fold
import PalamedesTest.Corpus.List.True.Fold

import PalamedesTest.Corpus.List.EvenLen.AccuOpt
import PalamedesTest.Corpus.List.LengthK.AccuOpt
import PalamedesTest.Corpus.List.True.AccuOpt

import PalamedesTest.Corpus.Tree.AllTwos.AllTwos
import PalamedesTest.Corpus.Tree.AVL.AVL
import PalamedesTest.Corpus.Tree.RBT.RBT
import PalamedesTest.Corpus.Tree.BadRBT.BadRBT
import PalamedesTest.Corpus.Tree.BST.BST
import PalamedesTest.Corpus.Tree.CompleteTree.CompleteTree
import PalamedesTest.Corpus.Tree.IncreasingByOne.IncreasingByOne
import PalamedesTest.Corpus.Tree.MaxDepth.MaxDepth
import PalamedesTest.Corpus.Tree.Nonempty.Nonempty

import PalamedesTest.Corpus.Tree.AllTwos.Fold
import PalamedesTest.Corpus.Tree.AVL.Fold
import PalamedesTest.Corpus.Tree.RBT.Fold
import PalamedesTest.Corpus.Tree.BadRBT.Fold
import PalamedesTest.Corpus.Tree.BST.Fold
import PalamedesTest.Corpus.Tree.CompleteTree.Fold
import PalamedesTest.Corpus.Tree.IncreasingByOne.Fold
import PalamedesTest.Corpus.Tree.MaxDepth.Fold
import PalamedesTest.Corpus.Tree.Nonempty.Fold

import PalamedesTest.Corpus.Stack.GoodStack
import PalamedesTest.Corpus.Stack.Fold

-- The Stage-5 demo: a datatype the library does not have, derived and synthesized end-to-end
-- from one `derive_palamedes` line, with zero edits to any `Palamedes/` module.
import PalamedesTest.Corpus.LeafTree.LeafTree

import PalamedesTest.Corpus.STLC.WellTyped.WellTyped
import PalamedesTest.Corpus.STLC.WellScoped.WellScoped

import PalamedesTest.Corpus.STLC.WellTyped.Fold
import PalamedesTest.Corpus.STLC.WellScoped.Fold
