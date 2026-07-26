/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.PGen

/-!
# Statistics for Palamedes generators

Basalt's `#genstats` command draws from a generator many times and summarizes the distribution it
produces (see `Basalt.GenStats`). Its interpretation monad, `GenStats.StatGen`, is an instance of
Basalt's `Gen` typeclass, so a generator declared at a **Basalt shape needs no adapter at all**:

```
#genstats (genBST 0 10)
#genstats (draws := 3000) (fuel := 10000) (genWellTyped [])
```

What a `Palamedes.PGen` additionally needs is a `Fail` instance, which this file provides, plus
`toStatGen` to name the interpretation. Three real lines, and only the carrier shape pays them:

```
#genstats (toStatGen genAtTheCarrier)
```

The report separates a failing `assume` (a terminating `failed` draw, so `ok` is an acceptance rate)
from `fuel-exhausted` (divergence) — a distinction the `SPMF` semantics cannot make, since both are
bottom there.

Output is seed-deterministic, so it works under `#guard_msgs`: see `PalamedesTest/Stats.lean`
and `PalamedesTest/Optimizer/Schedule.lean`.
-/

namespace Palamedes

/-- Computable failure for the statistics interpretation: a terminating failed draw, counted
    separately from fuel exhaustion. -/
instance : Fail GenStats.StatGen := ⟨throw (.failure "PGen.empty")⟩

/-- Interpret `g` at the statistics monad, for use with `#genstats`. -/
def toStatGen (g : PGen α) : GenStats.StatGen α := g.run

end Palamedes
