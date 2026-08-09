/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Synthesizer

/-!
# Corpus: An Index into a list, or Zero
-/

open Palamedes

/--
info: Try this:
  [apply] exact
    if hb : decide (List.length (List.idxsOf v xs) > 0) = true then
      frequency [(1, fun x => pure 0), (1, fun x => (TGen.elements (List.idxsOf v xs)).run)]
    else pure 0
-/
#guard_msgs in
def genIdxOrZero (xs : List Nat) (v : Nat) [Gen G] : G Nat := by
  generator_search? (fun n => n = 0 ∨ xs[n]? = some v)

/-- The pinned term above, pasted verbatim. -/
def genIdxOrZeroPasted (xs : List Nat) (v : Nat) [Gen G] : G Nat :=
  if hb : decide (List.length (List.idxsOf v xs) > 0) = true then
    frequency [(1, fun x => pure 0), (1, fun x => (TGen.elements (List.idxsOf v xs)).run)]
  else pure 0
