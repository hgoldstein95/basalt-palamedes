/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Synthesizer
import Palamedes.Data.List
import Palamedes.Data.Nat
import Palamedes.Sample
import Palamedes.Stats

/-!
# Tuning regression: a `Tuning` binder is threaded through synthesis

**The signature says whether a generator is tunable.** A `θ : Tuning` binder in scope is threaded
through every choice site by `installTuning`, run inside the pipeline between optimize and totality;
no binder means the generator ships uniform. There is no command and no flag.

Two properties carry the design, and both are pinned below:

* **One generator, one law.** `sound_complete` is `∀ … θ, …` because `θ` is one of the
  declaration's own binders, so the support invariant across every weighting is the *ordinary* law
  rather than a separate `tuned_support`/`tuned_sound_complete` pair. Nothing here relates two
  independently-derived generators, so there is no fidelity check to perform.
* **`.uniform` is universal.** `Tuning.weight` reads `θ.schedules.getD i (1, 0)`, so the empty
  tuning is the uniform weighting of *any* generator. That is what lets `(θ : Tuning := .uniform)`
  be written before the site count is known, and what makes the untuned call site mention tuning
  nowhere.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

/-! ## The carrier shape -/

/--
info: @[correct] genAllTwos: emitted sound_complete, total, correct
-/
#guard_msgs in
@[correct] def genAllTwos (θ : Tuning := .uniform) : Palamedes.PGen (List Nat) := by
  generator_search (fun xs => isAllTwos xs)

/--
info: @genAllTwos.sound_complete : ∀ (θ : optParam Tuning Tuning.uniform),
  (genAllTwos θ).support = fun xs => isAllTwos xs = true
-/
#guard_msgs in
#check @genAllTwos.sound_complete
/--
info: 'genAllTwos.sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms genAllTwos.sound_complete
/--
info: #[{ name := `genAllTwos.site0, offset := 0, arity := 2, holes := #[0, 1] }]
-/
#guard_msgs in
#eval genAllTwos.sites
/--
info: { schedules := #[(1, 12), (3, 0)] }
-/
#guard_msgs in
#eval SchedulePolicy.moderate.materialize genAllTwos.sites

-- The law is usable at any weighting, from the one theorem.
example (P : List Nat → Prop) (hP : (fun xs => isAllTwos xs = true) = P) (θ : Tuning) :
    (genAllTwos θ).support = P := by rw [genAllTwos.sound_complete θ, hP]

-- `.uniform` is the default, so the untuned call names no tuning.
/--
info: (toStatGen genAllTwos) — 500 draws (seed 0, fuel 5000)

  outcomes    ok 500 (100.0%)
  size        mean 1.9   p50 1   p95 4   max 8
  choices     mean 1.9   p50 1   p95 4   max 8
  distinct    8 / 500

  head constructor
    nil     50.4%  (252)
    cons    49.6%  (248)

  most common
     50.4%  (252)  []
     23.6%  (118)  [2]
     14.2%   (71)  [2, 2]
      7.8%   (39)  [2, 2, 2]
      2.0%   (10)  [2, 2, 2, 2]

  samples
    [2, 2]
    []
    []
-/
#guard_msgs in
#genstats (draws := 500) (fuel := 5000) (toStatGen genAllTwos)

-- A policy shifts the distribution. Support is unchanged — that is the theorem above.
/--
info: (toStatGen (genAllTwos (SchedulePolicy.moderate.materialize genAllTwos.sites))) — 500 draws (seed 0, fuel 5000)

  outcomes    ok 500 (100.0%)
  size        mean 1.9   p50 2   p95 3   max 4
  choices     mean 1.9   p50 2   p95 3   max 4
  distinct    4 / 500

  head constructor
    cons    72.4%  (362)
    nil     27.6%  (138)

  most common
     57.4%  (287)  [2]
     27.6%  (138)  []
     13.8%   (69)  [2, 2]
      1.2%    (6)  [2, 2, 2]

  samples
    [2, 2]
    [2, 2]
    []
-/
#guard_msgs in
#genstats (draws := 500) (fuel := 5000)
  (toStatGen (genAllTwos (SchedulePolicy.moderate.materialize genAllTwos.sites)))

/-! ## No `Tuning` binder is a legitimate signature: uniform, and no site table -/

def genUntuned : Palamedes.PGen (List Nat) := by generator_search (fun xs => isAllTwos xs)

run_cmd do
  if (← Lean.getEnv).contains `genUntuned.sites then
    throwError "genUntuned declared no `Tuning` binder, so no site table should be emitted"

/-! ## The Basalt shapes, tuned in place

There is no carrier companion and no re-projection: the generator is tuned *before* it is packaged,
so the `TGen` witness is built once, over the θ-open term. `total_frequency` never inspects weights,
which is why stage 4 closes exactly as it does for a uniform generator. -/

/--
info: @[correct] genLawfulB: emitted sound_complete
-/
#guard_msgs in
@[correct] def genLawfulB (θ : Tuning := .uniform) [Gen G] : G (List Nat) := by
  generator_search (fun xs => isAllTwos xs)

/--
info: @genLawfulB.sound_complete : ∀ (θ : optParam Tuning Tuning.uniform),
  IsSoundAndComplete (genLawfulB θ) fun xs => isAllTwos xs = true
-/
#guard_msgs in
#check @genLawfulB.sound_complete
/--
info: 'genLawfulB.sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms genLawfulB.sound_complete
/--
info: genLawfulB — 30 draws (seed 0, fuel 10000)

  outcomes    ok 30 (100.0%)
  size        mean 1.8   p50 1   p95 4   max 5
  choices     mean 1.8   p50 1   p95 4   max 5
  distinct    5 / 30

  head constructor
    nil     53.3%  (16)
    cons    46.7%  (14)

  most common
     53.3%  (16)  []
     23.3%   (7)  [2]
     13.3%   (4)  [2, 2]
      6.7%   (2)  [2, 2, 2]

  samples
    [2, 2]
    []
    []

  laws: sound_complete ✓
        terminates      — (not proved; measured 0/30 divergences)
        cost_bounded    — (not proved)
        filter_free     — (not proved)
        productive      — (not proved)
-/
#guard_msgs in
#genstats (draws := 30) genLawfulB
/--
info: (genLawfulB (SchedulePolicy.moderate.materialize genLawfulB.sites)) — 30 draws (seed 0, fuel 10000)

  outcomes    ok 30 (100.0%)
  size        mean 1.9   p50 2   p95 3   max 3
  choices     mean 1.9   p50 2   p95 3   max 3
  distinct    3 / 30

  head constructor
    cons    73.3%  (22)
    nil     26.7%   (8)

  most common
     56.7%  (17)  [2]
     26.7%   (8)  []
     16.7%   (5)  [2, 2]

  samples
    [2, 2]
    [2, 2]
    []

  laws: sound_complete ✓
        terminates      — (not proved; measured 0/30 divergences)
        cost_bounded    — (not proved)
        filter_free     — (not proved)
        productive      — (not proved)
-/
#guard_msgs in
#genstats (draws := 30) (genLawfulB (SchedulePolicy.moderate.materialize genLawfulB.sites))

/-! ## The filtering shape

Declared **without** a `Tuning` binder, and that is not an oversight. This generator synthesizes to
an `assume` over a `choose` with no `oneOf` anywhere, so there is no choice site for a `θ` to reach
and the binder would be dead — Lean's own unused-variable linter says so, which is the right tool
reporting it.

Filtering *and* branching is covered by `Corpus/Tree/AVL/AVL.lean`, which tags the recursive
filtering `genAVL`. That combination used to leave the `someSupport` bridge with an unsolved goal —
not for want of a twin, but because the bridge could not case-split the step generator's nested
conditionals to reach them. Fixed in `Synthesizer/Correct.lean`. The old `derive_tuning` suite
claimed to cover the tuned filtering path but tuned a site-free generator, so the claim was
vacuous. -/

/--
info: @[correct] genRangeB: emitted sound_complete
-/
#guard_msgs in
@[correct] def genRangeB (lo hi : Nat) [Gen G] : G (Option Nat) := by
  generator_search (fun n => lo ≤ n ∧ n ≤ hi)

run_cmd do
  if (← Lean.getEnv).contains `genRangeB.sites then
    throwError "genRangeB has no choice sites, so no site table should be emitted"

/--
info: genRangeB.sound_complete : ∀ (lo hi : ℕ), IsSomeSoundAndComplete (genRangeB lo hi) fun n => lo ≤ n ∧ n ≤ hi
-/
#guard_msgs in
#check @genRangeB.sound_complete
/--
info: 'genRangeB.sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms genRangeB.sound_complete

#eval show IO Unit from do
  let n ← Palamedes.samplePartial (genRangeB 3 7)
  unless 3 ≤ n && n ≤ 7 do throw <| IO.userError s!"genRangeB produced {n}, outside [3,7]"

/-! ## Binder order

`θ` is found by *type*, so it can sit anywhere in the telescope — including after `[Gen G]`, which
`declBinders` and `forallTelescope` both order the same way. -/

/--
info: @[correct] genFlipB: emitted sound_complete
-/
#guard_msgs in
@[correct] def genFlipB [Gen G] (_n : Nat) (θ : Tuning := .uniform) : G (List Nat) := by
  generator_search (fun xs => isAllTwos xs)

/--
info: @genFlipB.sound_complete : ∀ (_n : ℕ) (θ : optParam Tuning Tuning.uniform),
  IsSoundAndComplete (genFlipB _n θ) fun xs => isAllTwos xs = true
-/
#guard_msgs in
#check @genFlipB.sound_complete
