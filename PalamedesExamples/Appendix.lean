import Palamedes.Synthesizer

-- The synthesized halves are pasted verbatim, and the emitted step function binds its depth as `d`
-- whether or not the body reads it. Renaming to `_d` would break that fidelity, so the linter is
-- off rather than the paste being edited.
set_option linter.unusedVariables false

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

/-!
The synthesized halves below are `generator_search?` output, pasted verbatim. Two shapes recur in
every one of them, so they are noted here rather than repeated in each comparison:

- The synthesizer emits a **uniform `oneOf` over a list**, where a hand-written generator reaches
  for the binary `pick`.
- Recursive cases round-trip through an **identity `match` on the base functor** (`match tv with
  | ListF.nil => pure ListF.nil | ...`), an artifact of the fusion the search performs. A person
  writes the collector directly.
-/

def genOneOrInRange (lo hi : Nat) : Gen Nat :=
  if h : decide (lo ≤ hi) = true then Gen.oneOf [pure 0, choose lo hi] else pure 0

/-
Differences:
- Test the bound in `Prop` form rather than as `decide _ = true`.
-/
def genOneOrInRange_manual (lo hi : Nat) : Gen Nat :=
  if h : lo <= hi then
    pick (pure 0) (choose lo hi (by omega))
  else
    pure 0

def genCompleteTree (n : Nat) : Gen (Palamedes.Tree Nat) :=
  Palamedes.Tree.unfold
    (fun d p => do
      let tv ←
        if p.2 = 0 then pure TreeF.leaf
          else do
            let a ← arbNat
            pure (TreeF.node PUnit.unit a PUnit.unit)
      match tv with
        | TreeF.leaf => pure TreeF.leaf
        | TreeF.node a1 a2 a3 => pure (TreeF.node (a1, p.2 - 1) a2 (a3, p.2 - 1)))
    (PUnit.unit, n)

/-
Differences:
- Remove extra unit in collector.
-/
def genComplete_manual (n : Nat) : Gen (Palamedes.Tree Nat) :=
  Palamedes.Tree.unfold
    (fun _d height =>
      if height = 0 then
        pure TreeF.leaf
      else do
        let a <- arbNat
        pure (TreeF.node (height - 1) a (height - 1)))
    n

def genSortedBetween (lo hi : Nat) : Gen (List Nat) :=
  List.unfold
    (fun d p => do
      let tv ←
        if h : decide (p.2.1 ≤ p.2.2) = true then
            Gen.oneOf
              [pure ListF.nil, do
                let a ← choose p.2.1 p.2.2
                pure (ListF.cons a PUnit.unit)]
          else pure ListF.nil
      match tv with
        | ListF.nil => pure ListF.nil
        | ListF.cons a1 a2 => pure (ListF.cons a1 (a2, a1, p.2.2)))
    (PUnit.unit, lo, hi)

/-
Differences:
- Test the bound in `Prop` form rather than as `decide _ = true`.
- Remove extra unit in collector.
-/
def genSortedBetween_manual (lo hi : Nat) : Gen (List Nat) :=
  List.unfold
    (fun _d (lo, hi) =>
      if h : lo <= hi then
        pick
          (pure ListF.nil)
          (do
            let a <- choose lo hi (by omega)
            pure (ListF.cons a (a, hi)))
      else
        pure ListF.nil)
    (lo, hi)

def genLengthKAllTwos (k : Nat): Gen (List Nat) :=
  List.unfold
    (fun d p => do
      let tv ← if p.1.1 = 0 then pure ListF.nil else pure (ListF.cons 2 (Nat.pred p.1.1, PUnit.unit))
      match tv with
        | ListF.nil => pure ListF.nil
        | ListF.cons a1 a2 => pure (ListF.cons a1 (a2, PUnit.unit, PUnit.unit)))
    ((k, PUnit.unit), PUnit.unit, PUnit.unit)

/-
Differences:
- Remove two extra units in collector.
-/
def genLengthKAllTwos_manual (k : Nat): Gen (List Nat) :=
  List.unfold
    (fun _d len =>
      if len = 0 then
        pure ListF.nil
      else
        pure (ListF.cons 2 (len - 1)))
    k

def genAVL (height lo hi : Nat) : Gen (Palamedes.Tree Nat) :=
  Palamedes.Tree.unfold
    (fun d p =>
      if p.2.1 = 0 then pure TreeF.leaf
      else
        if Nat.pred p.2.1 = 0 then do
          let tv ←
            if h : decide (p.2.2.1 ≤ p.2.2.2) = true then
                Gen.oneOf
                  [pure TreeF.leaf, do
                    let a ← choose p.2.2.1 p.2.2.2
                    pure (TreeF.node (PUnit.unit, PUnit.unit) a (PUnit.unit, PUnit.unit))]
              else pure TreeF.leaf
          match tv with
            | TreeF.leaf => pure TreeF.leaf
            | TreeF.node a1 a2 a3 =>
              pure (TreeF.node (a1, p.2.1 - 1, p.2.2.1, a2 - 1) a2 (a3, p.2.1 - 1, a2 + 1, p.2.2.2))
        else
          assume (decide (p.2.2.1 ≤ p.2.2.2)) fun h => do
            let a ← choose p.2.2.1 p.2.2.2
            pure
                (TreeF.node ((PUnit.unit, PUnit.unit), p.2.1 - 1, p.2.2.1, a - 1) a
                  ((PUnit.unit, PUnit.unit), p.2.1 - 1, a + 1, p.2.2.2)))
    ((PUnit.unit, PUnit.unit), height, lo, hi)

/-
Differences:
- Remove two extra units in collector.
- Nicer match on height to reduce some duplication.
- Reorder the seed to `(lo, hi, height)`, so the bounds a `choose` reads sit next to each other.
-/
def genAVL_manual (height lo hi : Nat) : Gen (Palamedes.Tree Nat) :=
  Palamedes.Tree.unfold
    (fun _d (lo, hi, height) => do
      match height with
      | 0 => pure TreeF.leaf
      | 1 =>
        if h : lo > hi then
          pure TreeF.leaf
        else do
          pick
            (pure TreeF.leaf)
            (do
              let a <- choose lo hi (by aesop)
              pure (TreeF.node (lo, a - 1, height - 1) a (a + 1, hi, height - 1)))
      | height' + 1 => do
        -- We cannot guarantee that lo <= hi at this stage.
        assume (lo <= hi) fun h => do
          let a <- choose lo hi (by aesop)
          pure (TreeF.node (lo, a - 1, height - 1) a (a + 1, hi, height - 1)))
    (lo, hi, height)

/-
Differences:
- Remove two extra units in collector.
- Nicer match on height to reduce some duplication.
- Generator is technically total now; this requires insight about the total number of values that
can appear in a tree of height k.

def genAVL_manual' (height lo hi : Nat) : Gen (Palamedes.Tree Nat) :=
  -- Guarantee that there are enough values in the range, given the height.
  assume (hi - lo > 2 ^ height) fun _ =>
    Palamedes.Tree.unfold
      (fun (lo, hi, height) => do
        match height with
        | 0 => pure TreeF.leaf
        | 1 =>
            pick
              (pure TreeF.leaf)
              (assume (lo <= hi) fun h => do  -- Will always succeed.
                -- Choose values so we never truncate the range to be too small.
                let a <- choose (lo + 2 ^ (height - 1)) (hi - 2 ^ (height - 1)) (by aesop)
                pure (TreeF.node (lo, a - 1, height - 1) a (a + 1, hi, height - 1)))
        | height' + 1 => do
          assume (lo <= hi) fun h => do -- Will always succeed.
            -- Choose values so we never truncate the range to be too small.
            let a <- choose (lo + 2 ^ (height - 1)) (hi - 2 ^ (height - 1)) (by aesop)
            pure (TreeF.node (lo, a - 1, height - 1) a (a + 1, hi, height - 1)))
      (lo, hi, height)
-/
