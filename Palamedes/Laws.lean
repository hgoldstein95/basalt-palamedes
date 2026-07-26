/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Total
import Palamedes.SomeSupport

/-!
# Bridging Palamedes' `support` to Basalt's law vocabulary

`@[correct]` emits laws in **Basalt's** names, not Palamedes'. The pipeline proves
`Palamedes.PGen.support g = P`; Basalt states soundness-and-completeness as
`IsSoundAndComplete (g : SPMF α) P`, i.e. `∀ a, a ∈ SPMF.support g ↔ P a`. These two lemmas are the
whole of the conversion, and they exist so the command can `mkAppM` them rather than assemble the
`funext`/`propext` plumbing at the `Expr` level.

Both are definitional on the `support` side — `PGen.support g` *is* `SPMF.support g.run` — so the only
real content is `=` on predicates becoming a pointwise `↔`.
-/

namespace Palamedes

open Palamedes.PGen

variable {α : Type} {P : α → Prop}

/-- The law for a generator emitted at the synthesis-internal carrier. -/
theorem isSoundAndComplete_of_support {g : PGen α} (h : g.support = P) :
    IsSoundAndComplete (g.run (G := SPMF)) P := by
  -- `IsSoundAndComplete` is a semireducible `def`; `intro` opens it (the idiom Basalt's own examples
  -- use), where `show`/`unfold` do not.
  intro a
  exact iff_of_eq (congrFun h a)

/-- The law for a generator emitted **Basalt-shaped**, from the totality witness.

This is the step that needs no parametricity: `t.toGen = g` gives `g.run (G := SPMF) = t.run
(G := SPMF)` by congruence, because both sides are the *same* instantiation of the same polymorphic
term. The filtering path has no counterpart — `totalize` runs the generator at `OptionT SPMF`, a
different instantiation, so the transfer does not go through. -/
theorem isSoundAndComplete_of_total {t : TGen α} {g : PGen α}
    (hw : t.toGen = g) (h : g.support = P) :
    IsSoundAndComplete (t.run (G := SPMF)) P := by
  subst hw
  intro a
  exact iff_of_eq (congrFun h a)

/-- Soundness and completeness for a **filtering** generator: the values it actually produces are
exactly `P`.

This one notion is *not* borrowed from Basalt, because Basalt has none to borrow — its
`IsSoundAndComplete` characterises the whole support, and a filtering generator's support contains
`none`, which carries no information about `P`. Constraining it either way would be wrong:
`none ∉ support` is false whenever the generator can fail, and `none ∈ support` is unprovable
without knowing that it can. So the law quantifies over `some` values only, and says nothing about
failure — which is exactly the guarantee `generator_search` establishes.

The natural home for this is Basalt, alongside `IsSoundAndComplete`; it lives here because that is
where the filtering path lives today. -/
def IsSomeSoundAndComplete (g : SPMF (Option α)) (P : α → Prop) : Prop :=
  ∀ a, some a ∈ SPMF.support g ↔ P a

/-- The law for a generator emitted on the **filtering** path.

Unlike `isSoundAndComplete_of_total` this does *not* transfer a fact across two instantiations of
one polymorphic term — `someSupport` is defined at `OptionT SPMF` to begin with, which is the same
interpretation `totalize` runs the emitted definition at. The parametricity gap is only in the
*global* `someSupport g = g.support`, and the pipeline discharges the instance it needs by simp over
the combinator twins instead. -/
theorem isSomeSoundAndComplete_of_someSupport {g : PGen α} (h : someSupport g = P) :
    IsSomeSoundAndComplete (PGen.totalize g (G := SPMF)) P :=
  fun a => iff_of_eq (congrFun h a)

end Palamedes
