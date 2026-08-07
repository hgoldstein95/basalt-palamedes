/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Basalt.PlausibleGen
import Plausible

/-!
# Executable sampling for Palamedes generators

**Most generators need nothing from this module.** A generator declared at `[Gen G] : G α` is a
Basalt generator, and Plausible runs one directly — there is no adapter, and `#genstats genFoo`
needs none either. What is left over is the *filtering* shape, `[Gen G] : G (Option α)`, whose draws
can be `none`; that is the whole of what this module is for.

Sampling interprets failure through the explicit `Option` layer at `Plausible.Gen`: a failed
`assume` is an ordinary `none` draw — the same failure the `SPMF`/`massSome` semantics reasons
about — rather than a separate `throw`-based `Fail` instance. That layer is already in the declared
type by the time a generator reaches this module, so these functions add only the retry.

The sampler **retries on failure**: a `none` draw is redrawn whole (a global restart, via
Plausible's `Gen.runUntil`) up to `maxAttempts` times, so a filtering generator samples instead of
failing on the first rejected path; only exhausting every attempt throws (`samplePartial`) or returns
`none` (`samplePartial?`). The acceptance rate is reported by `#genstats` (`ok` vs `failed`), so it
is a measurable tuning objective. Deep filtering regimes (`genRBT` at height ≥ 3, `genAVL` at height
≥ 5) have vanishing acceptance and will exhaust `maxAttempts` — reported, never a silent hang.

Retry recovers from *failure*, not *divergence*: `total` means assume-free, not almost-sure
termination, and a total but non-a.s.-terminating generator can still hang when sampled.
A `Tuning` binder plus a depth-decaying schedule is the practical (measured, not proved) fix — see
`PalamedesTest/Optimizer/Schedule.lean`.
-/

namespace Palamedes

/-- Surface a `none` draw as a `GenError` so `Gen.runUntil` can retry it. This is the only place
failure crosses from data into Plausible's error channel; everything above it is retry. -/
def ofOption (g : Plausible.Gen (Option α)) : Plausible.Gen α := do
  match ← g with
  | some a => return a
  | none   => throw Plausible.Gen.genericFailure

/-- Draw a single value from `g`, **retrying on failure** up to `maxAttempts` times (a global
  restart via Plausible's `Gen.runUntil`). A filtering generator whose `assume` fails is redrawn
  rather than failing; only if all `maxAttempts` draws fail does this throw "out of attempts". -/
def samplePartial (g : Plausible.Gen (Option α))
    (size : Nat := 100) (maxAttempts : Nat := 1000) : IO α :=
  Plausible.Gen.runUntil (some maxAttempts) (ofOption g) size

/-- Like `samplePartial`, but returns `none` when all `maxAttempts` draws fail rather than throwing.
  The `some`/`none` rate over many draws is an empirical acceptance rate (`massSome`). -/
def samplePartial? (g : Plausible.Gen (Option α))
    (size : Nat := 100) (maxAttempts : Nat := 1000) : IO (Option α) := do
  try
    return some (← samplePartial g size maxAttempts)
  catch _ =>
    return none

/-- Draw `n` values from `g`, each with retry. -/
def samplePartialN (n : Nat) (g : Plausible.Gen (Option α))
    (size : Nat := 100) (maxAttempts : Nat := 1000) : IO (List α) :=
  (List.replicate n ()).mapM (fun _ => samplePartial g size maxAttempts)

end Palamedes
