/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Basalt.PlausibleGen
import Plausible

/-!
# Executable Sampling for Palamedes Generators

The retry loop for the filtering shape `[Gen G] : G (Option α)`.
-/

namespace Palamedes

/-- Surface a `none` draw as a `GenError` so `Gen.runUntil` can retry it. This is the only place
failure crosses from data into Plausible's error channel; everything above it is retry. -/
def ofOption (g : Plausible.Gen (Option α)) : Plausible.Gen α := do
  match ← g with
  | some a => return a
  | none   => throw Plausible.Gen.genericFailure

/-- Draw a single value from `g`, retrying on failure up to `maxAttempts` times (a global
restart via Plausible's `Gen.runUntil`). -/
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
