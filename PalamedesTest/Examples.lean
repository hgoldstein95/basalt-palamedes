/-
Aggregates the full example corpus. Compiling this module elaborates every example, each of which
synthesizes a generator at elaboration time and *fails to compile* if synthesis fails — so this
file is the de facto test suite. `PalamedesTest.ExtractionAudit` imports it to walk the corpus.
-/

import PalamedesTest.Examples.Simple.Eq2
import PalamedesTest.Examples.Simple.Eq2'
import PalamedesTest.Examples.Simple.Eq2Or5
import PalamedesTest.Examples.Simple.Eq2Or5'
import PalamedesTest.Examples.Simple.OneOfFour
import PalamedesTest.Examples.Simple.ThreePlusOne

import PalamedesTest.Examples.Tuple.Pairs

import PalamedesTest.Examples.Range.Between5And10
import PalamedesTest.Examples.Range.BetweenLoAndHi
import PalamedesTest.Examples.Range.Gt5
import PalamedesTest.Examples.Range.ZeroOrInRange

import PalamedesTest.Examples.Arbitrary
import PalamedesTest.Examples.OptimizationTests

import PalamedesTest.Examples.List.AllTwos.AllTwos
import PalamedesTest.Examples.List.AllTwosEvenLen.AllTwosEvenLen
import PalamedesTest.Examples.List.AllEvens.Evens
import PalamedesTest.Examples.List.EvenLen.EvenLen
import PalamedesTest.Examples.List.IncreasingByOne.IncreasingByOne
import PalamedesTest.Examples.List.LengthK.LengthK
import PalamedesTest.Examples.List.LengthKAllTwos.LengthKAllTwos
import PalamedesTest.Examples.List.SortedBetween.SortedBetween
import PalamedesTest.Examples.List.True.True

import PalamedesTest.Examples.List.AllTwos.Fold
import PalamedesTest.Examples.List.AllTwosEvenLen.Fold
import PalamedesTest.Examples.List.AllEvens.Fold
import PalamedesTest.Examples.List.EvenLen.Fold
import PalamedesTest.Examples.List.IncreasingByOne.Fold
import PalamedesTest.Examples.List.LengthK.Fold
import PalamedesTest.Examples.List.LengthKAllTwos.Fold
import PalamedesTest.Examples.List.SortedBetween.Fold
import PalamedesTest.Examples.List.True.Fold

import PalamedesTest.Examples.List.EvenLen.AccuOpt
import PalamedesTest.Examples.List.LengthK.AccuOpt
import PalamedesTest.Examples.List.True.AccuOpt

import PalamedesTest.Examples.Tree.AllTwos.AllTwos
import PalamedesTest.Examples.Tree.AVL.AVL
import PalamedesTest.Examples.Tree.RBT.RBT
import PalamedesTest.Examples.Tree.BadRBT.BadRBT
import PalamedesTest.Examples.Tree.BST.BST
import PalamedesTest.Examples.Tree.CompleteTree.CompleteTree
import PalamedesTest.Examples.Tree.IncreasingByOne.IncreasingByOne
import PalamedesTest.Examples.Tree.MaxDepth.MaxDepth
import PalamedesTest.Examples.Tree.Nonempty.Nonempty

import PalamedesTest.Examples.Tree.AllTwos.Fold
import PalamedesTest.Examples.Tree.AVL.Fold
import PalamedesTest.Examples.Tree.RBT.Fold
import PalamedesTest.Examples.Tree.BadRBT.Fold
import PalamedesTest.Examples.Tree.BST.Fold
import PalamedesTest.Examples.Tree.CompleteTree.Fold
import PalamedesTest.Examples.Tree.IncreasingByOne.Fold
import PalamedesTest.Examples.Tree.MaxDepth.Fold
import PalamedesTest.Examples.Tree.Nonempty.Fold

import PalamedesTest.Examples.Stack.GoodStack
import PalamedesTest.Examples.Stack.Fold

-- The Stage-5 demo: a datatype the library does not have, derived and synthesized end-to-end
-- from one `derive_palamedes` line, with zero edits to any `Palamedes/` module.
import PalamedesTest.Examples.LeafTree.LeafTree

import PalamedesTest.Examples.STLC.WellTyped.WellTyped
import PalamedesTest.Examples.STLC.WellScoped.WellScoped

import PalamedesTest.Examples.STLC.WellTyped.Fold
import PalamedesTest.Examples.STLC.WellScoped.Fold
