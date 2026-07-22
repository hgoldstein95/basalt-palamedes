/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Lean

/-!
# The `extract` and `totality_witness` Simp Sets

Both turn synthesis artifacts back into generator code: `extract` pulls the raw `PGen` out of a
`CorrectGen` term (one `.val` equation per synthesis combinator), and `totality_witness` projects a
totality witness (`witness.val.run`) down to the underlying Basalt combinators.
-/

register_simp_attr extract
register_simp_attr totality_witness
