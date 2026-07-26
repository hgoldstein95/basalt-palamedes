/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer

/-!
# Corpus: an index into a list, or zero

Synthesizes `genIdxOrZero xs v : G Nat` for `fun n => n = 0 ∨ xs[n]? = some v`. The disjunct on the
right is the shape that reaches `elements`, and the one on the left is what makes the generator
total: the `assume` guarding the draw has a sibling that always succeeds, so the optimizer floats it
into a `dite` rather than leaving it to filter.

That combination — a bound guard, and under it a primitive whose side-condition proof is discharged
*from* that guard — is what `genWellTyped` is built out of, four times over, and nothing else in the
corpus exercises it. This file is the small version, small enough to pin the emitted term and to
paste it back; `genWellTyped` itself is pinned by `#genstats` instead, so its printing is unguarded.

Both halves of the pin matter, and neither implies the other. `TGen.elements` must print **without**
its nonemptiness proof, which is `delabElements`; and `genIdxOrZeroPasted` must elaborate from
exactly that text, which is `gen_side_condition` recovering the proof from `hb`. Dropping a proof
the autoParam cannot rebuild gives a term that does not compile, and printing one gives a term
naming a synthesis-internal `._proof_i`.

What this file does *not* reach is the identity proof transport `extractWitness` strips: the
generator is too shallow for simp to introduce one. `genWellTyped`, whose guard sits under a
recursion and a `caseTy` match, is where that shows.
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
