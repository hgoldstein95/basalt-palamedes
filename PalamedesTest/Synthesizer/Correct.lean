/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer
import Palamedes.Data.List
import Palamedes.Data.Nat
import PalamedesTest.Harness

/-!
# `@[correct]` regression

The synthesizer's proofs survive into the environment. Every law below is **kernel-checked** by
`addDecl`, which is the property that matters.

`#print axioms` is the load-bearing assertion in this file — it is what distinguishes a real proof
from one that merely elaborated.
-/

open Palamedes

namespace PalamedesTest.Synthesizer.Correct

@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

/-- info: @[correct] PalamedesTest.Synthesizer.Correct.genAllTwos: emitted sound_complete -/
#guard_msgs in
@[correct] def genAllTwos [Gen G] : G (List Nat) := by generator_search (fun xs => isAllTwos xs)

-- Nothing wraps it: this is the same `∀ {G} [Gen G], G α` a hand-written Basalt generator has.
/-- info: @genAllTwos : {G : Type → Type} → [Gen G] → G (List ℕ) -/
#guard_msgs in
#check @genAllTwos

-- The law is stated against the emitted *constant*, so it is a fact about `genAllTwos` rather than
-- about a copy of its body. It is in **Basalt's** vocabulary, and it is about `genAllTwos` at
-- `SPMF` — `G` and its instance are supplied rather than generalized, since a law over an
-- uninstantiated `G` would mention a binder its statement never uses.
/-- info: genAllTwos.sound_complete : IsSoundAndComplete genAllTwos fun xs => isAllTwos xs = true -/
#guard_msgs in
#check @genAllTwos.sound_complete

/-- info: 'PalamedesTest.Synthesizer.Correct.genAllTwos.sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms genAllTwos.sound_complete

-- The law is usable: a support fact now transfers from a *named* theorem rather than having to be
-- re-established. This is the whole point of emitting it.
example (P : List Nat → Prop) (hP : (fun xs => isAllTwos xs = true) = P) :
    IsSoundAndComplete (genAllTwos (G := SPMF)) P := by
  rw [← hP]; exact genAllTwos.sound_complete

-- There is no `genAllTwos.total`: the declared type is `G (List ℕ)`, which is `Fail`-free by
-- construction, so totality is what the *type* says and not a companion to state it again. A
-- generator that could fail would not have elaborated at this shape at all.
run_cmd
  PalamedesTest.assertNotDeclared `PalamedesTest.Synthesizer.Correct.genAllTwos.total
    "totality is the content of a `G α` declaration, not a companion beside it"

/-! ## Binders

Binders are Lean's, not ours — which is the point of being an attribute rather than a command. The
`[Gen G]` binder is what makes the shape Basalt's (and `G` is auto-bound, never written), and value
binders are quantified over in the emitted law.
-/

-- Value binders are *kept*, and the law quantifies over them.
/-- info: @[correct] PalamedesTest.Synthesizer.Correct.genParam: emitted sound_complete -/
#guard_msgs in
@[correct] def genParam (_n : Nat) [Gen G] : G (List Nat) := by
  generator_search (fun xs => isAllTwos xs)

/--
info: genParam.sound_complete : ∀ (_n : ℕ), IsSoundAndComplete (genParam _n) fun xs => isAllTwos xs = true
-/
#guard_msgs in
#check @genParam.sound_complete

-- The filtering shape takes binders too, and carries a law of its own.
/-- info: @[correct] PalamedesTest.Synthesizer.Correct.genRange: emitted sound_complete -/
#guard_msgs in
@[correct] def genRange (lo hi : Nat) [Gen G] : G (Option Nat) := by
  generator_search (fun n => lo ≤ n ∧ n ≤ hi)

/-- info: @genRange : {G : Type → Type} → ℕ → ℕ → [Gen G] → G (Option ℕ) -/
#guard_msgs in
#check @genRange

-- The filtering law is `IsSomeSoundAndComplete`, not Basalt's `IsSoundAndComplete`: the support of
-- a generator that can fail contains `none`, which says nothing about `P`. So the law quantifies
-- over the `some` values — exactly what the search establishes — and is silent about failure.
/--
info: genRange.sound_complete : ∀ (lo hi : ℕ), IsSomeSoundAndComplete (genRange lo hi) fun n => lo ≤ n ∧ n ≤ hi
-/
#guard_msgs in
#check @genRange.sound_complete

/-- info: 'PalamedesTest.Synthesizer.Correct.genRange.sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms genRange.sound_complete

-- A non-recursive generator over a `Prop`-valued predicate. This one regression-guards the
-- optimizer's assume-discharge: `support_assume_true` is stated at `b := true` precisely so its
-- proof carries no unassigned metavariable, and `@[correct]` on it is what detects a relapse —
-- the kernel rejects a declaration containing metavariables, so the failure is loud. The literal
-- bounds are what make it discharge: `3 ≤ n ∧ n ≤ 7` leaves no `assume`, so this elaborates at
-- `G ℕ` rather than `G (Option ℕ)`.
/-- info: @[correct] PalamedesTest.Synthesizer.Correct.genBetween: emitted sound_complete -/
#guard_msgs in
@[correct] def genBetween [Gen G] : G Nat := by generator_search (fun n => 3 ≤ n ∧ n ≤ 7)

/-- info: PalamedesTest.Synthesizer.Correct.genBetween.sound_complete : IsSoundAndComplete genBetween fun n => 3 ≤ n ∧ n ≤ 7 -/
#guard_msgs in
#check genBetween.sound_complete

/-- info: 'PalamedesTest.Synthesizer.Correct.genBetween.sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms genBetween.sound_complete

end PalamedesTest.Synthesizer.Correct
