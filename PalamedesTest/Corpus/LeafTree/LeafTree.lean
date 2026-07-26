/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Stage-5 demo: a brand-new datatype, end-to-end, from one line

`LeafTree` exists nowhere in the Palamedes library. `derive_palamedes` generates its entire
recursion-scheme template *and* registers it with the synthesizer (the `unfold_strategy`
registry), so `generator_search` synthesizes correct-by-construction generators for it with
**zero edits** to any `Palamedes/` module.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

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

def genAllTwos [Gen G] : G (LeafTree Nat) := by
  generator_search (fun t => isAllTwos t)

@[simp]
def isAllTwosFold (t : LeafTree Nat) : Bool :=
  LeafTree.fold (fun x => x == 2) (fun bl br => bl && br) t

def genAllTwosFold [Gen G] : G (LeafTree Nat) := by
  generator_search (fun t => isAllTwosFold t = true)

-- Complete of depth exactly `d`: a `σ → Bool` function-carrier fold with state threading.
@[simp]
def isCompleteFold (t : LeafTree Nat) (d : Nat) : Bool :=
  LeafTree.fold (fun _ s => s == 0) (fun bl br s => decide (s > 0) && bl (s - 1) && br (s - 1)) t d

/--
info: Try this:
  [apply] exact
    LeafTree.unfoldGo
      (fun d x => do
        let a ←
          if x.2 = 0 then do
              let a ← TGen.arbNat.run
              pure (LeafTreeF.tip a)
            else pure (LeafTreeF.branch PUnit.unit PUnit.unit)
        match a with
          | LeafTreeF.tip a1 => pure (LeafTreeF.tip a1)
          | LeafTreeF.branch a1 a2 => pure (LeafTreeF.branch (a1, x.2 - 1) (a2, x.2 - 1)))
      0 (PUnit.unit, d)
-/
#guard_msgs in
def genCompleteFold (d : Nat) [Gen G] : G (LeafTree Nat) := by
  generator_search? (fun t => isCompleteFold t d = true)

end LeafTreeDemo
