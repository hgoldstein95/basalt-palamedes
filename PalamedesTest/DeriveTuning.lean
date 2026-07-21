/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Synthesizer
import Palamedes.DeriveTuning
import Palamedes.Stats
import Palamedes.Sample
import Palamedes.Data.List

/-!
# `derive_tuning` structural regression

Guards the command's output on a small generator — the site table, the uniform defaults, the
`SchedulePolicy → Tuning` round-trip, and that a tuned generator samples. The tuned *distribution* of
a real generator is guarded separately in `ScheduleMeasurements.lean`.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

def genAllTwos : Palamedes.PGen (List Nat) := by
  generator_search (fun xs => isAllTwos xs)

-- `derive_tuning` reports what it emitted, and names what it did not: `genAllTwos` is a plain
-- `def`, so it has no `sound_complete` and there is no law to carry across every `θ`.
/--
info: derive_tuning genAllTwos: emitted tuned, defaults, sites, tuned_defaults, tuned_support
  (no `tuned_sound_complete`: genAllTwos has no `sound_complete` to carry across — declare it with `correct def` to get one)
-/
#guard_msgs in
derive_tuning genAllTwos

-- The four declarations exist at the right types; `tuned_defaults` is definitional.
/-- info: genAllTwos.tuned : Tuning → PGen (List ℕ) -/
#guard_msgs in
#check (genAllTwos.tuned : Tuning → Palamedes.PGen (List Nat))

/-- info: genAllTwos.tuned_defaults : genAllTwos.tuned genAllTwos.defaults = genAllTwos -/
#guard_msgs in
#check (genAllTwos.tuned_defaults : genAllTwos.tuned genAllTwos.defaults = genAllTwos)

-- The tuned generator carries the `support = P` invariant at *every* `θ`, not just at the defaults:
-- this is `installTuning`'s per-site `support_oneOf_reweight` proof, surfaced instead of discarded.
/-- info: genAllTwos.tuned_support (θ : Tuning) : (genAllTwos.tuned θ).support = genAllTwos.support -/
#guard_msgs in
#check genAllTwos.tuned_support

-- The intended use: whatever support fact you hold about the plain generator transfers to *every*
-- tuning of it, so `support = P` is stable under reweighting rather than re-established per `θ`.
example (P : List Nat → Prop) (hP : genAllTwos.support = P) (θ : Tuning) :
    (genAllTwos.tuned θ).support = P := by
  rw [genAllTwos.tuned_support, hP]

/-- info: #[{ name := `genAllTwos.site0, offset := 0, arity := 2, holes := #[0, 1] }] -/
#guard_msgs in
#eval genAllTwos.sites

/-- info: { schedules := #[(1, 0), (1, 0)] } -/
#guard_msgs in
#eval genAllTwos.defaults

-- The round-trip tripwire: a materialized policy is a plain `Tuning`, one entry per branch keyed on
-- its recursive-child count (`moderate` = `decayBy 3 12`: leaf `(1, 12)`, recursive `(3, 0)`).
/-- info: { schedules := #[(1, 12), (3, 0)] } -/
#guard_msgs in
#eval SchedulePolicy.moderate.materialize genAllTwos.sites

-- The tuned generator samples, and the moderate schedule decays it with depth.
/--
info: (toStatGen (genAllTwos.tuned (SchedulePolicy.moderate.materialize genAllTwos.sites))) — 500 draws (seed 0, fuel 5000)

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
  (toStatGen (genAllTwos.tuned (SchedulePolicy.moderate.materialize genAllTwos.sites)))

/-! ## A plain-`def` Basalt-shaped generator is rejected, and says why

The tuning layer rewrites the `Palamedes.PGen` carrier; a Basalt-shaped declaration is a projection
of it, and only `correct def` keeps the carrier around (`generator_search` is a tactic and never
learns a declaration name). A plain `def` therefore has nothing to tune, and the error names the
fix rather than failing deep inside `buildTuned` as a type mismatch.
-/

def genTwosBasalt [Gen G] : G (List Nat) := by generator_search (fun xs => isAllTwos xs)

/--
error: derive_tuning: genTwosBasalt is Basalt-shaped and has no carrier companion (genTwosBasalt.gen) to tune.

The tuning layer rewrites the `Palamedes.PGen` carrier, and the Basalt shape is a projection of it — `generator_search` is a tactic and never learns a declaration name, so only `correct def` keeps the carrier around. Re-declare it as

  correct def genTwosBasalt … := by generator_search …

and `derive_tuning genTwosBasalt` will tune the companion and re-project.
-/
#guard_msgs in
derive_tuning genTwosBasalt

/-! ## The Basalt shape is tuned through its carrier companion

`correct def` emits `f.gen : Palamedes.PGen α` alongside the projection; `derive_tuning f` tunes the
companion with the unchanged carrier machinery, re-runs the `totality` cascade on the θ-open tuned
term (`total_frequency` never inspects weights), projects the fresh witness back to generator code,
and transfers the law across the witness equation. The generator, its law, and its weights are one
artifact — at the Basalt shape.
-/

/-- info: correct def genLawfulB: emitted (generator), sound_complete, gen -/
#guard_msgs in
correct def genLawfulB [Gen G] : G (List Nat) := by
  generator_search (fun xs => isAllTwos xs)

/--
info: derive_tuning genLawfulB: emitted tuned, defaults, sites, tuned_sound_complete
  (tuned at the carrier: see genLawfulB.gen.tuned_support and friends; `tuned_defaults` exists only there — two totality witnesses of one generator are not definitionally equal)
-/
#guard_msgs in
derive_tuning genLawfulB

-- The projected `tuned` has the declaration's own shape, θ first.
/-- info: genLawfulB.tuned : Tuning → {G : Type → Type} → [Gen G] → G (List ℕ) -/
#guard_msgs in
#check @genLawfulB.tuned

-- The law is about the projected constant at `SPMF`, for every `θ`, and is axiom-clean.
/--
info: genLawfulB.tuned_sound_complete : ∀ (θ : Tuning), IsSoundAndComplete (genLawfulB.tuned θ) fun xs => isAllTwos xs = true
-/
#guard_msgs in
#check @genLawfulB.tuned_sound_complete

/--
info: 'genLawfulB.tuned_sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms genLawfulB.tuned_sound_complete

-- The projected tuned generator *runs*, under Basalt's own tooling, weights supplied.
/--
info: (genLawfulB.tuned genLawfulB.defaults) — 30 draws (seed 0, fuel 10000)

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
-/
#guard_msgs in
#genstats (draws := 30) (genLawfulB.tuned genLawfulB.defaults)

-- θ is actually threaded through the re-projection. There is no Basalt-level `tuned_defaults` to
-- pin that (see the note above), and `tuned_sound_complete` is support-only, so it would hold
-- vacuously of a projection that dropped `θ` on the floor. A decaying schedule shifts the head
-- constructor split away from the uniform run above; that shift is the assertion.
/--
info: (genLawfulB.tuned (SchedulePolicy.moderate.materialize genLawfulB.sites)) — 30 draws (seed 0, fuel 10000)

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
-/
#guard_msgs in
#genstats (draws := 30)
  (genLawfulB.tuned (SchedulePolicy.moderate.materialize genLawfulB.sites))

-- Value binders are kept, and the tuned law quantifies over them (after `θ`).
/-- info: correct def genParamB: emitted (generator), sound_complete, gen -/
#guard_msgs in
correct def genParamB (_n : Nat) [Gen G] : G (List Nat) := by
  generator_search (fun xs => isAllTwos xs)

/--
info: derive_tuning genParamB: emitted tuned, defaults, sites, tuned_sound_complete
  (tuned at the carrier: see genParamB.gen.tuned_support and friends; `tuned_defaults` exists only there — two totality witnesses of one generator are not definitionally equal)
-/
#guard_msgs in
derive_tuning genParamB

/--
info: genParamB.tuned_sound_complete : ∀ (θ : Tuning) (_n : ℕ),
  IsSoundAndComplete (genParamB.tuned θ _n) fun xs => isAllTwos xs = true
-/
#guard_msgs in
#check @genParamB.tuned_sound_complete

/--
info: 'genParamB.tuned_sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms genParamB.tuned_sound_complete

/-! ## The filtering shape is tuned too, through `totalize`

A `G (Option α)` declaration has no totality witness to rebuild — the projection is `totalize` of
the tuned companion, and the law is `IsSomeSoundAndComplete`, discharged through the same
`someSupport` bridge `correct def` uses, now on a term whose weights are opaque `θ`-reads.
-/

/-- info: correct def genRangeB: emitted (generator), sound_complete, gen -/
#guard_msgs in
correct def genRangeB (lo hi : Nat) [Gen G] : G (Option Nat) := by
  generator_search (fun n => lo ≤ n ∧ n ≤ hi)

/--
info: derive_tuning genRangeB: emitted tuned, defaults, sites, tuned_sound_complete
  (tuned at the carrier: see genRangeB.gen.tuned_support and friends; `tuned_defaults` exists only there — two totality witnesses of one generator are not definitionally equal)
-/
#guard_msgs in
derive_tuning genRangeB

/--
info: genRangeB.tuned_sound_complete : ∀ (θ : Tuning) (lo hi : ℕ),
  IsSomeSoundAndComplete (genRangeB.tuned θ lo hi) fun n => lo ≤ n ∧ n ≤ hi
-/
#guard_msgs in
#check @genRangeB.tuned_sound_complete

/--
info: 'genRangeB.tuned_sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms genRangeB.tuned_sound_complete

-- And it samples, in range, through the retry loop.
#eval show IO Unit from do
  let n ← Palamedes.samplePartial (genRangeB.tuned genRangeB.defaults 3 7)
  unless 3 ≤ n && n ≤ 7 do
    throw <| IO.userError s!"genRangeB.tuned produced {n}, outside [3,7]"

/-! ## Binder order

Re-projection drops `G` and its `[Gen G]` instance and applies the companion to what is left.
`correct def` built the companion's telescope by the same filter, so the two agree — but they are
written out in two files, and only an instance-last arrangement was ever exercised. Here the
instance comes *first*, so a positional (rather than by-type) filter on either side mis-applies the
companion and this stops elaborating.
-/

/-- info: correct def genFlipB: emitted (generator), sound_complete, gen -/
#guard_msgs in
correct def genFlipB [Gen G] (_n : Nat) : G (List Nat) := by
  generator_search (fun xs => isAllTwos xs)

/--
info: derive_tuning genFlipB: emitted tuned, defaults, sites, tuned_sound_complete
  (tuned at the carrier: see genFlipB.gen.tuned_support and friends; `tuned_defaults` exists only there — two totality witnesses of one generator are not definitionally equal)
-/
#guard_msgs in
derive_tuning genFlipB

/--
info: genFlipB.tuned_sound_complete : ∀ (θ : Tuning) (_n : ℕ),
  IsSoundAndComplete (genFlipB.tuned θ _n) fun xs => isAllTwos xs = true
-/
#guard_msgs in
#check @genFlipB.tuned_sound_complete

/-! ## A companion without a law: tuned, but reported as lawless

`correct def` always emits `f.gen` and `f.gen.sound_complete` together, so this arrangement is not
reachable through it — the companion here is hand-written. That is the point: the "no
`tuned_sound_complete`" branch is otherwise unreachable from the whole build, and it is the branch
that has to say *why* rather than skip the law silently.
-/

def genManualB [Gen G] : G (List Nat) := by generator_search (fun xs => isAllTwos xs)

def genManualB.gen : Palamedes.PGen (List Nat) := genAllTwos

/--
info: derive_tuning genManualB: emitted tuned, defaults, sites
  (no `tuned_sound_complete`: genManualB.gen has no `sound_complete` to carry across)
  (tuned at the carrier: see genManualB.gen.tuned_support and friends; `tuned_defaults` exists only there — two totality witnesses of one generator are not definitionally equal)
-/
#guard_msgs in
derive_tuning genManualB

-- The generator and its weights are still emitted; only the law is missing.
/-- info: genManualB.tuned : Tuning → {G : Type → Type} → [Gen G] → G (List ℕ) -/
#guard_msgs in
#check @genManualB.tuned

run_cmd do
  if (← Lean.getEnv).contains `genManualB.tuned_sound_complete then
    throwError "genManualB has no carrier law, so `tuned_sound_complete` must not be emitted"

/-! ## A non-generator constant is rejected -/

/--
error: derive_tuning: isAllTwos is neither a `Palamedes.PGen` nor a Basalt-shaped generator, so there is nothing here to reweight.
-/
#guard_msgs in
derive_tuning isAllTwos

/-! ## The law survives tuning

`correct def` establishes `support = P`; `derive_tuning` proves reweighting preserves the support at
every site. Chaining them gives the law in **Basalt's** vocabulary for *every* `θ`: a tuning changes
the distribution and provably not the set of values.
-/

/-- info: correct def genLawful: emitted (generator), sound_complete, total, correct -/
#guard_msgs in
correct def genLawful : Palamedes.PGen (List Nat) := by generator_search (fun xs => isAllTwos xs)

/--
info: derive_tuning genLawful: emitted tuned, defaults, sites, tuned_defaults, tuned_support, tuned_sound_complete
-/
#guard_msgs in
derive_tuning genLawful

/--
info: genLawful.tuned_sound_complete : ∀ (θ : Tuning),
  IsSoundAndComplete (genLawful.tuned θ).run fun xs => isAllTwos xs = true
-/
#guard_msgs in
#check @genLawful.tuned_sound_complete

/--
info: 'genLawful.tuned_sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms genLawful.tuned_sound_complete
