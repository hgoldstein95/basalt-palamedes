import Palamedes.Synthesizer
import Palamedes.DeriveTuning
import Palamedes.Stats
import Palamedes.Data.List

/-!
# `derive_tuning` structural regression

Guards the command's output on a small generator — the site table, the uniform defaults, the
`SchedulePolicy → Tuning` round-trip, and that a tuned generator samples. The tuned *distribution* of
a real generator is guarded separately in `ScheduleMeasurements.lean`.
-/

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

def genAllTwos : Palamedes.Gen (List Nat) := by
  generator_search (fun xs => isAllTwos xs)

derive_tuning genAllTwos

-- The four declarations exist at the right types; `tuned_defaults` is definitional.
/-- info: genAllTwos.tuned : Tuning → Palamedes.Gen (List ℕ) -/
#guard_msgs in
#check (genAllTwos.tuned : Tuning → Palamedes.Gen (List Nat))

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
