/-
Copyright (c) 2025 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Gen

/-!
# Failure-aware semantics for Palamedes generators

If a generator synthesizes with backtracking, we provide tools to lift it into a partial generator.
-/

namespace Palamedes

open Gen
open scoped ENNReal

instance instFailOptionT {G : Type → Type} [Monad G] : Fail (OptionT G) := ⟨OptionT.fail⟩

namespace Gen

/-- Interpret a (possibly failing) Palamedes generator as a **total** generator of `Option α`. -/
def totalize (g : Gen α) : ∀ {G : Type → Type} [_root_.Gen G], G (Option α) :=
  fun {_G} _ => OptionT.run (g.run (G := OptionT _G))

end Gen

end Palamedes
