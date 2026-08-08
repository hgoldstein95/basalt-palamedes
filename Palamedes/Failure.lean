/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.PGen

/-!
# Failure-aware semantics for Palamedes generators

If a generator synthesizes with backtracking, we provide tools to lift it to a generator at
`OptionT`.
-/

namespace Palamedes

open Palamedes.PGen
open scoped ENNReal

instance instFailOptionT {G : Type → Type} [Monad G] : Fail (OptionT G) := ⟨OptionT.fail⟩

namespace PGen

/-- Interpret a (possibly failing) Palamedes generator as a **total** generator of `Option α`.

Anything itself polymorphic in `G` commutes with this definitionally.
-/
def totalize (g : PGen α) : ∀ {G : Type → Type} [Gen G], G (Option α) :=
  fun {_G} _ => OptionT.run (g.run (G := OptionT _G))

end PGen

/-- Failure at `OptionT`, as the `Option`-valued draw it is: this is where reading a generator at
`OptionT G` turns its `Fail` capability into data.

An equation, so that one rewrite takes a rejecting branch all the way to Basalt vocabulary. Reducing
the instance instead — `Fail.fail`, `instFailOptionT`, `OptionT.fail` — stops at
`OptionT.mk (pure none)`, leaving the transformer's own constructor in a term that is meant to read
as a generator. -/
theorem run_fail {G : Type → Type} [Monad G] {α : Type} :
    (Fail.fail : OptionT G α) = (pure none : G (Option α)) := rfl

end Palamedes
