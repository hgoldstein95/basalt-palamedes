import Palamedes.Gen
import Palamedes.Failure
import Basalt.PlausibleGen
import Plausible

/-!
# Executable sampling for Palamedes generators

A `Palamedes.Gen α` is a thin wrapper around a polymorphic Basalt generator that may also fail
(`∀ {G} [Gen G] [Fail G], G α` — the `Fail` is what distinguishes it from `TGen`). We sample by
interpreting it through the **explicit `Option` layer** (`Gen.totalize`, `Palamedes/Failure.lean`):
`totalize g` at `Plausible.Gen` is a `Plausible.Gen (Option α)` in which a failed `assume` is an
ordinary `none` value. This is the *same* failure the `SPMF`/`massSome` semantics reasons about — one
uniform failure story (`Fail (OptionT G) := pure none`) across proofs and sampling — rather than a
separate `throw`-based `Fail Plausible.Gen`.

## Retry on failure (global restart)

A draw that yields `none` is a failed `assume`. The sampler **retries on failure**: it redraws the
whole value (a global restart, in the sense of Basalt's `SPMF.retry`) up to `maxAttempts`
times. We reuse Plausible's own `Gen.runUntil` for the loop, surfacing a `none` as a `GenError` only at
the boundary (`toPlausible`) so `runUntil` can drive it — the `throw` is a retry-loop mechanism, not
the generator's notion of failure. So a filtering generator — one declared at `G (Option α)` because
it contains a genuinely failing `assume`, e.g. `genAVL` or `genRBT` — *samples* instead of failing on the first
failing path. Only if **every** attempt fails does `sample` throw "out of attempts"; `sample?` returns
`none` in that case instead.

The acceptance rate (empirical `massSome`) is what governs how many attempts a draw needs; it is
reported directly by `#genstats` (the `ok` vs `failed` split), so it is a *measurable tuning
objective*, not a sampler-design problem. Deep filtering regimes (`genRBT` at height ≥ 3, `genAVL` at
height ≥ 5) have vanishing acceptance and will exhaust `maxAttempts` — that is intrinsic to the
generator, not the sampler, and it is *reported* (a thrown "out of attempts" / a `none`) rather than a
silent hang.

## Remaining limitation: divergence

Retry recovers from *failure* (`none`), not *divergence*. `total` here means *assume-free*, not
almost-sure termination; a total but non-a.s.-terminating generator can still hang when sampled.
`derive_tuning` + a depth-decaying `Tuning` is the practical answer — depth-indexed schedules took
`genWellTyped` from diverging on 54.3% of draws to 0/3000 (see `PalamedesTest/ScheduleMeasurements`).
It is a *measured* fix, not a proved one; nothing yet certifies a.s. termination.
-/

namespace Palamedes

open _root_.Palamedes.Gen

/-- Surface a `none` draw as a `GenError` so `Gen.runUntil` can retry it.

This is the entry point for a generator that is **already** `Option`-reflected by its own type — the
shape `generator_search` now emits for a filtering generator, where the `Option` in the declared
return type is what `allow_partial` used to say. `toPlausible` is this composed with `totalize`, so
the two paths share one retry story rather than duplicating it. -/
def ofOption (g : Plausible.Gen (Option α)) : Plausible.Gen α := do
  match ← g with
  | some a => return a
  | none   => throw Plausible.Gen.genericFailure

/-- Interpret `g` at Plausible's `Gen` monad through the explicit `Option` layer: a failed `assume`
  becomes a `none` value (matching the `massSome` semantics), which we surface as a `GenError` at
  this boundary only so that `Gen.runUntil` can retry it. -/
def toPlausible (g : Gen α) : Plausible.Gen α :=
  ofOption (totalize g)

/-- Draw a single value from `g`, **retrying on failure** up to `maxAttempts` times (a global
  restart via Plausible's `Gen.runUntil`). A filtering generator whose `assume` fails is redrawn
  rather than failing; only if all `maxAttempts` draws fail does this throw "out of attempts". -/
def sample (g : Gen α) (size : Nat := 100) (maxAttempts : Nat := 1000) : IO α :=
  Plausible.Gen.runUntil (some maxAttempts) (toPlausible g) size

/-- Like `sample`, but returns `none` when all `maxAttempts` draws fail rather than throwing. The
  `some`/`none` rate over many draws is an empirical acceptance rate (`massSome`). -/
def sample? (g : Gen α) (size : Nat := 100) (maxAttempts : Nat := 1000) : IO (Option α) := do
  try
    return some (← sample g size maxAttempts)
  catch _ =>
    return none

/-- Draw `n` values from `g`, each with retry. -/
def sampleN (n : Nat) (g : Gen α) (size : Nat := 100) (maxAttempts : Nat := 1000) : IO (List α) :=
  (List.replicate n ()).mapM (fun _ => sample g size maxAttempts)

/-! ### Sampling a filtering generator

A generator synthesized at `G (Option α)` has already been through `totalize`, so it needs the retry
loop but not the reflection. These are the `sample*` family one layer in. -/

/-- `sample` for a generator whose type already says it can fail. -/
def samplePartial (g : Plausible.Gen (Option α))
    (size : Nat := 100) (maxAttempts : Nat := 1000) : IO α :=
  Plausible.Gen.runUntil (some maxAttempts) (ofOption g) size

/-- `sample?` for a generator whose type already says it can fail. -/
def samplePartial? (g : Plausible.Gen (Option α))
    (size : Nat := 100) (maxAttempts : Nat := 1000) : IO (Option α) := do
  try
    return some (← samplePartial g size maxAttempts)
  catch _ =>
    return none

/-- `sampleN` for a generator whose type already says it can fail. -/
def samplePartialN (n : Nat) (g : Plausible.Gen (Option α))
    (size : Nat := 100) (maxAttempts : Nat := 1000) : IO (List α) :=
  (List.replicate n ()).mapM (fun _ => samplePartial g size maxAttempts)

end Palamedes
