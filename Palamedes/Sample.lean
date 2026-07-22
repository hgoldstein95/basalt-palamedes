/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.PGen
import Palamedes.Failure
import Basalt.PlausibleGen
import Plausible

/-!
# Executable sampling for Palamedes generators

Sampling interprets a `PGen` through the explicit `Option` layer (`PGen.totalize`) at
`Plausible.Gen`: a failed `assume` is an ordinary `none` draw — the same failure the
`SPMF`/`massSome` semantics reasons about — rather than a separate `throw`-based `Fail` instance.

The sampler **retries on failure**: a `none` draw is redrawn whole (a global restart, via
Plausible's `Gen.runUntil`) up to `maxAttempts` times, so a filtering generator samples instead of
failing on the first rejected path; only exhausting every attempt throws (`sample`) or returns
`none` (`sample?`). The acceptance rate is reported by `#genstats` (`ok` vs `failed`), so it is a
measurable tuning objective. Deep filtering regimes (`genRBT` at height ≥ 3, `genAVL` at height
≥ 5) have vanishing acceptance and will exhaust `maxAttempts` — reported, never a silent hang.

Retry recovers from *failure*, not *divergence*: `total` means assume-free, not almost-sure
termination, and a total but non-a.s.-terminating generator can still hang when sampled.
`derive_tuning` plus a depth-decaying `Tuning` is the practical (measured, not proved) fix — see
`PalamedesTest/Optimizer/Schedule.lean`.
-/

namespace Palamedes

open Palamedes.PGen

/-- Surface a `none` draw as a `GenError` so `Gen.runUntil` can retry it.

This is the entry point for a generator that is **already** `Option`-reflected by its own type — the
shape `generator_search` emits for a filtering generator. `toPlausible` is this composed with
`totalize`, so
the two paths share one retry story rather than duplicating it. -/
def ofOption (g : Plausible.Gen (Option α)) : Plausible.Gen α := do
  match ← g with
  | some a => return a
  | none   => throw Plausible.Gen.genericFailure

/-- Interpret `g` at Plausible's `Gen` monad through the explicit `Option` layer: a failed `assume`
  becomes a `none` value (matching the `massSome` semantics), which we surface as a `GenError` at
  this boundary only so that `Gen.runUntil` can retry it. -/
def toPlausible (g : PGen α) : Plausible.Gen α :=
  ofOption (totalize g)

/-- Draw a single value from `g`, **retrying on failure** up to `maxAttempts` times (a global
  restart via Plausible's `Gen.runUntil`). A filtering generator whose `assume` fails is redrawn
  rather than failing; only if all `maxAttempts` draws fail does this throw "out of attempts". -/
def sample (g : PGen α) (size : Nat := 100) (maxAttempts : Nat := 1000) : IO α :=
  Plausible.Gen.runUntil (some maxAttempts) (toPlausible g) size

/-- Like `sample`, but returns `none` when all `maxAttempts` draws fail rather than throwing. The
  `some`/`none` rate over many draws is an empirical acceptance rate (`massSome`). -/
def sample? (g : PGen α) (size : Nat := 100) (maxAttempts : Nat := 1000) : IO (Option α) := do
  try
    return some (← sample g size maxAttempts)
  catch _ =>
    return none

/-- Draw `n` values from `g`, each with retry. -/
def sampleN (n : Nat) (g : PGen α) (size : Nat := 100) (maxAttempts : Nat := 1000) : IO (List α) :=
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
