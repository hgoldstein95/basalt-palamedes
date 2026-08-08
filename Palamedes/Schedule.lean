/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Basalt

/-!
# Depth-indexed weight schedules

A `SchedulePolicy` proposes, per branch, an affine weight schedule `wⱼ(d) = aⱼ + bⱼ · d`, so mean
offspring can start above 1 near the root and fall below 1 with depth. Decay is base-weight *growth*,
never recursive-weight shrinkage: a weight of `0` would drop its branch from the support, so every
weight stays `≥ 1` and a deep recursion becomes rarer, never impossible.

Schedules are pure `Tuning`-producing data — `SchedulePolicy.materialize` lays a policy over a site
table into a Basalt `Tuning`. The `installTuning` optimizer pass that *reads* such a `Tuning` at each
`frequency` site lives in `Palamedes.Tuning`, and the synthesis pipeline drives it; nothing here
depends on the optimizer.
-/

/-- When tunings are left empty, the system defaults to uniform. -/
def Tuning.uniform : Tuning := ⟨#[]⟩

attribute [simp] Tuning.weight_pos

namespace Palamedes

/-- An affine weight schedule `d ↦ base + growth · d`. Invariant: `base ≥ 1`. The `(base, growth)`
pair is exactly one entry of a Basalt `Tuning`; a `SchedulePolicy` produces these per branch and
`SchedulePolicy.materialize` lays them out into a `Tuning`. -/
structure Schedule where
  base : Nat
  growth : Nat
  deriving Repr, Inhabited

/-- How to weight a branch, as a function of how many recursive children it has.

A policy is untrusted: it can only tune the distribution, never the support, since the
support-preservation proof is composed regardless of what it proposes. -/
structure SchedulePolicy where
  weight : Nat → Schedule

/-- A general, datatype-agnostic decay family, keyed only on whether a branch *closes* the recursion.

Continuing branches (≥1 recursive child) are held at the constant `root`; closing branches (0
children) grow as `1 + rate·d`. So at the root the recursion is favored `root : 1` — mean offspring
starts supercritical when `root > 1` — and as depth grows the closing branches dominate and mean
offspring falls to 0, forcing termination. Two knobs, both interpretable:

* `root` — how bushy the top of the value is (the root branching bias);
* `rate` — how fast the recursion is driven closed with depth.

Unlike `SchedulePolicy.stlc` this makes no per-arity distinction, so it carries no tuning specific to
any one datatype. The named points below (`gentle`/`moderate`/`steep`) are the ready-made choices. -/
def SchedulePolicy.decayBy (root rate : Nat) : SchedulePolicy where
  weight
    | 0 => { base := 1, growth := rate }
    | _ => { base := root, growth := 0 }

/-- Slow decay: the recursion stays live several levels down, giving deeper and larger values. -/
def SchedulePolicy.gentle : SchedulePolicy := .decayBy 3 4

/-- A general-purpose middle decay rate: supercritical at the root, closed within a few levels. -/
def SchedulePolicy.moderate : SchedulePolicy := .decayBy 3 12

/-- Fast decay: the recursion closes almost immediately, giving shallow values that terminate hard. -/
def SchedulePolicy.steep : SchedulePolicy := .decayBy 3 30

/-- The STLC-tuned policy: a branch that closes the recursion grows fastest with depth, one with a
single child grows more slowly, and a branch with two or more is held constant — decayed *relative
to* the others, never toward zero.

The coefficients are hand-tuned on `genWellTyped`, and its distribution is pinned in
`PalamedesTest/Schedule.lean`; this is *not* a good general default (it encodes an arity preference
specific to STLC's term type). Materialize it against a generator's sites with
`SchedulePolicy.stlc.materialize gen.sites` and pass the result to the generator's own `Tuning`
binder (see `Palamedes.Tuning`).
Eventually a drift solve should compute coefficients like these per site. -/
def SchedulePolicy.stlc : SchedulePolicy where
  weight
    | 0 => { base := 1, growth := 30 }
    | 1 => { base := 1, growth := 14 }
    | _ => { base := 4, growth := 0 }

/-- Lay a `SchedulePolicy` over a site table into a `Tuning`: each branch's `(base, growth)` is
`policy.weight` of its recursive-child count (`Site.holes`), placed at flat index `offset + j`. Turns
a coarse arity-keyed policy into the per-site `Tuning` a tuned generator reads. -/
def SchedulePolicy.materialize (policy : SchedulePolicy) (sites : Array Site) : Tuning := Id.run do
  let total := sites.foldl (init := 0) fun acc s => max acc (s.offset + s.arity)
  let mut arr : Array (Nat × Nat) := Array.replicate total (1, 0)
  for s in sites do
    for j in [0:s.arity] do
      let sched := policy.weight (s.holes.getD j 0)
      arr := arr.set! (s.offset + j) (sched.base, sched.growth)
  return ⟨arr⟩

end Palamedes
