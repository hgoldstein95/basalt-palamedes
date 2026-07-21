/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.PGen

/-!
# Failure-aware semantics for Palamedes generators

If a generator synthesizes with backtracking, we provide tools to lift it into a partial generator.
-/

namespace Palamedes

open Palamedes.PGen
open scoped ENNReal

instance instFailOptionT {G : Type → Type} [Monad G] : Fail (OptionT G) := ⟨OptionT.fail⟩

namespace PGen

/-- Interpret a (possibly failing) Palamedes generator as a **total** generator of `Option α`. -/
def totalize (g : PGen α) : ∀ {G : Type → Type} [Gen G], G (Option α) :=
  fun {_G} _ => OptionT.run (g.run (G := OptionT _G))

end PGen

end Palamedes
