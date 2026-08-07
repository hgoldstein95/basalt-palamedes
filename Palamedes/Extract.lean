/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Lean

/-!
# The `extract`, `totality_witness` and `partial_witness` Simp Sets

All three turn a synthesis artifact back into generator code, one per stage that has to:

* `extract` pulls the raw `PGen` out of a `CorrectGen` term — one `.val` equation per synthesis
  combinator;
* `totality_witness` projects a totality witness (`witness.val.run`) down to the Basalt combinators
  underneath, for a generator declared `G α`;
* `partial_witness` pushes `.run` through a generator that kept an `assume`, reading it at
  `OptionT G`, for a generator declared `G (Option α)`.

Each is a *set* rather than a `Meta.reduce` because the stages must stop in different places: full
reduction would unfold Basalt's `frequency` into `frequencyAux`, and a datatype's primitive into its
recursion scheme, neither of which reads as a generator.
-/

register_simp_attr extract
register_simp_attr totality_witness
register_simp_attr partial_witness
