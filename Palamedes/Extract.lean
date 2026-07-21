/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Lean

register_simp_attr extract

/-- Simp set that turns a **totality witness** back into generator code.

`generator_search` emits a Basalt-shaped generator as `witness.val.run`. Left unreduced that is a
tree of `total_*` applications — a proof, not a generator — which defeats the point of Palamedes
emitting *readable* generators. These lemmas project `.val` through each witness constructor and
then unfold `TGen.run` to the underlying Basalt combinator, so what lands in the environment is the
generator itself. Exactly analogous to `extract`, which pulls a `PGen` out of a `CorrectGen`.

Every one holds by `rfl`, which is precisely what the data-first shape of the `total_*` defs buys:
tactics in the data path would leave an `Eq.rec` that blocks the projection.
-/
register_simp_attr twitness
