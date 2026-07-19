import Palamedes.Synthesizer

/-!
# Stage-5 demo: a brand-new datatype, end-to-end, from one line

`LeafTree` exists nowhere in the Palamedes library. `derive_palamedes` generates its entire
recursion-scheme template *and* registers it with the synthesizer (the `unfold_strategy`
registry), so `generator_search` synthesizes correct-by-construction generators for it with
**zero edits** to any `Palamedes/` module.
-/

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace LeafTreeDemo

inductive LeafTree (α : Type) where
  | tip (x : α)
  | branch (l : LeafTree α) (r : LeafTree α)

derive_palamedes LeafTree

-- All tips carry a 2: a plain `Bool`-carrier fold (recursive predicate + fold-form variant).
@[simp]
def isAllTwos : LeafTree Nat → Bool
  | .tip x => x == 2
  | .branch l r => isAllTwos l && isAllTwos r

def genAllTwos : Gen (LeafTree Nat) := by
  generator_search (fun t => isAllTwos t)

@[simp]
def isAllTwosFold (t : LeafTree Nat) : Bool :=
  LeafTree.fold (fun x => x == 2) (fun bl br => bl && br) t

def genAllTwosFold : Gen (LeafTree Nat) := by
  generator_search (fun t => isAllTwosFold t = true)

-- Complete of depth exactly `d`: a `σ → Bool` function-carrier fold with state threading.
@[simp]
def isCompleteFold (t : LeafTree Nat) (d : Nat) : Bool :=
  LeafTree.fold (fun _ s => s == 0) (fun bl br s => decide (s > 0) && bl (s - 1) && br (s - 1)) t d

def genCompleteFold (d : Nat) : Gen (LeafTree Nat) := by
  generator_search (fun t => isCompleteFold t d = true)

end LeafTreeDemo
