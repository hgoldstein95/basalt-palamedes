/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Sample
import PalamedesTest.Corpus.Tree.AVL.AVL
import PalamedesTest.Corpus.Tree.RBT.RBT

/-!
# Sampler tests: filtering generators sample instead of throwing

The headline of the failure-aware semantics: a filtering generator — one declared at `G (Option α)`
because it has a genuinely failing `assume` — is *sampled* through the retry loop (`samplePartial`)
rather than throwing a `GenError` on the first
failing path. Each `#eval` below draws for real during the build and throws — failing the build — on
an unexpected outcome.

The retrying assertions are statistically safe, not razor-thin: the lowest acceptance rate exercised
here is `genAVL 4` at ~8% per draw (measured), so 1000 attempts fail with
probability below 10⁻³⁰. Deep filtering regimes (`genRBT 3+`, `genAVL 5+`) have vanishing acceptance
and are deliberately *not* asserted; the out-of-attempts path is pinned with `PGen.empty`, which fails
deterministically.
-/

open Palamedes Palamedes.PGen

/- `genAVL 3` never fails (measured 100% acceptance): a draw must succeed. -/
#eval show IO Unit from do
  let t ← Palamedes.samplePartial (AVL.genAVL 3 0 10)
  unless (AVL.isAVL 3 0 10 t) do
    throw <| IO.userError s!"genAVL 3 produced a non-AVL tree"

/- `genAVL 4` is a real filter (~8% acceptance): retry makes it sample anyway, and the result
still satisfies the predicate — retry only conditions the distribution, it cannot leave the
support. -/
#eval show IO Unit from do
  let t ← Palamedes.samplePartial (AVL.genAVL 4 0 100)
  unless (AVL.isAVL 4 0 100 t) do
    throw <| IO.userError s!"genAVL 4 produced a non-AVL tree"

/- `genRBT 2` filters at ~23% acceptance; the retry loop is what makes it sample. -/
#eval show IO Unit from do
  let t ← Palamedes.samplePartial (RBT.genRBT 2 0 10)
  unless (RBT.isRBT t 2 0 10) do
    throw <| IO.userError s!"genRBT 2 produced a non-RBT tree"

/- The out-of-attempts path, deterministically: `PGen.empty` fails every draw, so `sample?` reports
`none` instead of hanging or crashing the build. -/
#eval show IO Unit from do
  match ← Palamedes.sample? (PGen.empty : PGen Nat) (maxAttempts := 10) with
  | none => pure ()
  | some n => throw <| IO.userError s!"sample? PGen.empty produced {n}"

/- The throwing variant `sample` reports exhaustion as an error rather than returning. -/
#eval show IO Unit from do
  match ← (Palamedes.sample (PGen.empty : PGen Nat) (maxAttempts := 10)).toBaseIO with
  | .error _ => pure ()
  | .ok n => throw <| IO.userError s!"sample PGen.empty produced {n}"

/-! ## The `samplePartial` family

The `Plausible.Gen (Option α)` layer, entered directly by a generator whose declared type already
says it can fail. Same three behaviours as the `sample` family above, one layer in.
-/

/- Exhaustion at the partial layer: every draw is `none`, so `samplePartial?` returns `none`. -/
#eval show IO Unit from do
  match ← Palamedes.samplePartial? (pure none : Plausible.Gen (Option Nat)) (maxAttempts := 10) with
  | none => pure ()
  | some n => throw <| IO.userError s!"samplePartial? (pure none) produced {n}"

/- ...and `samplePartial` throws on the same generator rather than returning a junk value. -/
#eval show IO Unit from do
  let g : Plausible.Gen (Option Nat) := pure none
  match ← (Palamedes.samplePartial g (maxAttempts := 10)).toBaseIO with
  | .error _ => pure ()
  | .ok n => throw <| IO.userError s!"samplePartial (pure none) produced {n}"

/- `samplePartialN` draws exactly `n`, retrying each independently. `genRangeB`-style filtering is
covered in `DeriveTuning`; here the point is the count and that every element cleared the filter. -/
#eval show IO Unit from do
  let ts ← Palamedes.samplePartialN 3 (RBT.genRBT 2 0 10)
  unless ts.length = 3 do
    throw <| IO.userError s!"samplePartialN 3 produced {ts.length} elements"
  unless ts.all (fun t => RBT.isRBT t 2 0 10) do
    throw <| IO.userError "samplePartialN 3 produced a non-RBT tree"
