/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer
import Palamedes.Data.List
import Palamedes.Data.Nat
import Palamedes.Stats

/-!
# `@[correct]` regression

The synthesizer's proofs survive into the environment. Every law below is **kernel-checked** by
`addDecl`, which is the property that matters.

`#print axioms` is the load-bearing assertion in this file — it is what distinguishes a real proof
from one that merely elaborated.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

/-- info: @[correct] genAllTwos: emitted sound_complete, total, correct -/
#guard_msgs in
@[correct] def genAllTwos : Palamedes.PGen (List Nat) := by generator_search (fun xs => isAllTwos xs)

-- The law is stated against the emitted *constant*, so it is a fact about `genAllTwos` rather than
-- about a copy of its body.
/-- info: genAllTwos.sound_complete : genAllTwos.support = fun xs => isAllTwos xs = true -/
#guard_msgs in
#check genAllTwos.sound_complete

/-- info: 'genAllTwos.sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms genAllTwos.sound_complete

/-- info: 'genAllTwos.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms genAllTwos.total

-- The law is usable: a support fact now transfers from a *named* theorem rather than having to be
-- re-established. This is the whole point of emitting it.
example (P : List Nat → Prop) (hP : (fun xs => isAllTwos xs = true) = P) :
    genAllTwos.support = P := by
  rw [genAllTwos.sound_complete, hP]

-- `f.correct` is the bundled view, for feeding `f` back into synthesis where the rules consume a
-- `CorrectGen`. It is a *view*, not a copy: `.val` is definitionally the declaration itself.
/-- info: genAllTwos.correct : CorrectGen fun xs => isAllTwos xs = true -/
#guard_msgs in
#check @genAllTwos.correct

example : genAllTwos.correct.val = genAllTwos := rfl

-- Totality is data, so the Basalt-shaped generator is a projection out of the law.
def genAllTwosBasalt [Gen G] : G (List Nat) := genAllTwos.total.val.run

-- `Palamedes/Laws.lean`'s other bridge: a `support = P` law at the internal carrier converts to
-- Basalt's vocabulary on demand. `@[correct]` does not emit this form — the declared shape is
-- Palamedes', so the law it emits is too — but the conversion is one application away.
example : IsSoundAndComplete (genAllTwos.run (G := SPMF)) (fun xs => isAllTwos xs = true) :=
  isSoundAndComplete_of_support genAllTwos.sound_complete

/-! ## Binders

Binders are Lean's, not ours — which is the point of being an attribute rather than a command. The
`[Gen G]` binder is what makes the shape Basalt's (and `G` is auto-bound, never written), and value
binders are quantified over in the emitted law.
-/

/-- info: @[correct] genBasalt: emitted sound_complete -/
#guard_msgs in
@[correct] def genBasalt [Gen G] : G (List Nat) := by generator_search (fun xs => isAllTwos xs)

-- Nothing wraps it: this is the same `∀ {G} [Gen G], G α` a hand-written Basalt generator has.
/-- info: @genBasalt : {G : Type → Type} → [Gen G] → G (List ℕ) -/
#guard_msgs in
#check @genBasalt

-- The law is in **Basalt's** vocabulary, and it is about `genBasalt` at `SPMF` — `G` and its
-- instance are supplied rather than generalized, since a law over an uninstantiated `G` would
-- mention a binder its statement never uses.
/-- info: genBasalt.sound_complete : IsSoundAndComplete genBasalt fun xs => isAllTwos xs = true -/
#guard_msgs in
#check @genBasalt.sound_complete

/-- info: 'genBasalt.sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms genBasalt.sound_complete

-- Value binders are *kept*, and the law quantifies over them.
/-- info: @[correct] genParam: emitted sound_complete, total, correct -/
#guard_msgs in
@[correct] def genParam (_n : Nat) : Palamedes.PGen (List Nat) := by
  generator_search (fun xs => isAllTwos xs)

/-- info: genParam.sound_complete : ∀ (_n : ℕ), (genParam _n).support = fun xs => isAllTwos xs = true -/
#guard_msgs in
#check @genParam.sound_complete

-- The filtering shape takes binders too, and it now carries a law of its own.
/-- info: @[correct] genRange: emitted sound_complete -/
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

/-- info: 'genRange.sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms genRange.sound_complete

-- The negative half of the emission report. `total` and `correct` are carrier-shape laws and a
-- filtering generator has no totality witness to state one from, so they must be *absent* — the
-- reported list above stays honest only if nothing is emitted behind it.
run_cmd do
  for suffix in [`total, `correct] do
    if (← Lean.getEnv).contains (`genRange ++ suffix) then
      throwError "genRange is filtering, so it has no totality witness and `genRange.{suffix}` \
        must not be emitted"

-- A non-recursive generator over a `Prop`-valued predicate. This one regression-guards the
-- optimizer's assume-discharge: `support_assume_true` is stated at `b := true` precisely so its
-- proof carries no unassigned metavariable, and `@[correct]` on it is what detects a relapse —
-- the kernel rejects a declaration containing metavariables, so the failure is loud.
/-- info: @[correct] genBetween: emitted sound_complete, total, correct -/
#guard_msgs in
@[correct] def genBetween : Palamedes.PGen Nat := by generator_search (fun n => 3 ≤ n ∧ n ≤ 7)

/-- info: genBetween.sound_complete : genBetween.support = fun n => 3 ≤ n ∧ n ≤ 7 -/
#guard_msgs in
#check genBetween.sound_complete

/-- info: 'genBetween.sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms genBetween.sound_complete
