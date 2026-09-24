/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Failure
import Palamedes.Support

/-!
# The support of a *filtering* generator

`PGen.support g` reads a generator at `SPMF`, where `Fail` is `⊥`, so it describes the values a
generator produces *when it does not fail*; a filtering generator's emitted definition runs the same
polymorphic term at `OptionT SPMF` instead. This file gives the support notion for *that*
interpretation (`someSupport`) and the lemmas the per-datatype twins need.
-/

namespace Palamedes

open Palamedes.PGen

variable {α β : Type}

/-- The support of a possibly-failing generator, read through `totalize` — the values it can
actually produce, as opposed to the values it produces when it does not fail.

There is no global `someSupport g = g.support` — it would be a free theorem about `g.run`'s
polymorphic type, which Lean does not prove. The agreement holds combinator-by-combinator (the
`@[simp]` lemmas below), so the per-datatype twins are *derived*, not transported. -/
def someSupport (g : PGen α) : α → Prop :=
  fun a => some a ∈ SPMF.support (PGen.totalize g (G := SPMF))

/-- Intro form for a `someSupport` equation, the `OptionT SPMF` counterpart of
`PGen.Support.support_ext`. -/
theorem someSupport_ext {g : PGen α} {P : α → Prop}
    (h : ∀ a, some a ∈ SPMF.support (PGen.totalize g (G := SPMF)) ↔ P a) : someSupport g = P :=
  funext fun a => propext (h a)

theorem support_optionT_pure (a : α) :
    SPMF.support (OptionT.run (pure a : OptionT SPMF α)) = {some a} := by
  rw [show (pure a : OptionT SPMF α) = OptionT.mk (Pure.pure (some a)) from rfl]
  simp [OptionT.run, OptionT.mk]

/-- The `bind` lemma. Note the `some` on both sides: a `none` from `x` cannot lead to a `some w`, so
the `none` branch drops out — which is exactly what makes the twins' scripts mirror the `SPMF` ones
rather than acquiring an extra case per bind. -/
theorem mem_support_optionT_bind {x : OptionT SPMF α} {k : α → OptionT SPMF β} {w : β} :
    some w ∈ SPMF.support (OptionT.run (x >>= k))
      ↔ ∃ a, some a ∈ SPMF.support (OptionT.run x)
              ∧ some w ∈ SPMF.support (OptionT.run (k a)) := by
  simp only [bind, OptionT.bind, OptionT.mk, OptionT.run]
  rw [SPMF.bind_eq]
  simp only [SPMF.mem_support_bind_iff]
  constructor
  · rintro ⟨o, ho, hw⟩
    cases o with
    | none =>
      exact absurd hw (by
        simp [Pure.pure, SPMF.support, SPMF.pure, DFunLike.coe])
    | some a => exact ⟨a, ho, hw⟩
  · rintro ⟨a, ha, hw⟩
    exact ⟨some a, ha, hw⟩

theorem mem_support_optionT_map {x : OptionT SPMF α} {g : α → β} {w : β} :
    some w ∈ SPMF.support (OptionT.run (g <$> x : OptionT SPMF β))
      ↔ ∃ a, some a ∈ SPMF.support (OptionT.run x) ∧ g a = w := by
  rw [show (g <$> x : OptionT SPMF β) = x >>= fun a => pure (g a) from rfl,
    mem_support_optionT_bind]
  simp only [support_optionT_pure, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ha, hw⟩; exact ⟨a, ha, (Option.some.inj hw).symm⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩

theorem mem_support_optionT_lift {p : SPMF α} {a : α} :
    some a ∈ SPMF.support (OptionT.run (OptionT.lift p : OptionT SPMF α))
      ↔ a ∈ SPMF.support p := by
  simp only [OptionT.lift, OptionT.mk, OptionT.run, SPMF.mem_support_bind_iff,
    SPMF.mem_support_pure_iff]
  constructor
  · rintro ⟨a', ha', hw⟩
    cases Option.some.inj hw; exact ha'
  · intro ha
    exact ⟨a, ha, rfl⟩

/-! ## The observation

`someSupport` is the may observation of the `OptionT SPMF` interpretation, so a choice combinator's
lemma is its `Obs.map_*` read through an angelic presentation — the derivation of
`SPMF.support_oneOf` and `SPMF.support_frequency`, one interpretation over. -/

/-- The may observation at `OptionT SPMF`: some value the generator can produce without failing
satisfies the postcondition. -/
def someObs : Obs (OptionT SPMF) (WP Mix.angelic) where
  spec g := fun Q => ∃ a, some a ∈ SPMF.support (OptionT.run g) ∧ Q a
  map_pure a := by
    funext Q; apply propext
    show (∃ b, some b ∈ SPMF.support (OptionT.run (pure a : OptionT SPMF _)) ∧ Q b) ↔ Q a
    simp
  map_bind x k := by
    funext Q; apply propext
    show (∃ b, some b ∈ SPMF.support (OptionT.run (x >>= k)) ∧ Q b)
      ↔ ∃ a, some a ∈ SPMF.support (OptionT.run x)
          ∧ ∃ b, some b ∈ SPMF.support (OptionT.run (k a)) ∧ Q b
    simp only [mem_support_optionT_bind]
    exact ⟨fun ⟨b, ⟨a, ha, hb⟩, h⟩ => ⟨a, ha, b, hb, h⟩,
      fun ⟨a, ha, b, hb, h⟩ => ⟨b, ⟨a, ha, hb⟩, h⟩⟩
  map_choose lo hi h := by
    funext Q; apply propext
    show (∃ a, some a ∈ SPMF.support (OptionT.run (OptionT.lift (RandomChoice.choose lo hi h)))
      ∧ Q a) ↔ ∃ a, Q a
    simp only [mem_support_optionT_lift, SPMF.mem_support_choose_iff, true_and]

/-- `some`-membership, read through a specification the observation equals. -/
theorem mem_support_optionT_of_obs {g : OptionT SPMF α} {w : WP Mix.angelic α}
    (h : someObs.spec g = w) {a : α} : some a ∈ SPMF.support (OptionT.run g) ↔ w (· = a) :=
  ⟨fun ha => h ▸ ⟨a, ha, rfl⟩, fun hw => by obtain ⟨_, hb, e⟩ := h ▸ hw; exact e ▸ hb⟩

theorem mem_support_optionT_oneOf {gs : List (Unit → OptionT SPMF α)} (hne : gs ≠ []) {w : α} :
    some w ∈ SPMF.support (OptionT.run (oneOf gs hne))
      ↔ ∃ g ∈ gs, some w ∈ SPMF.support (OptionT.run (g ())) :=
  (mem_support_optionT_of_obs (someObs.map_oneOf gs hne)).trans
    ((Mix.index_angelic gs hne fun g => someObs.spec (g ()) (· = w)).trans
      (exists_congr fun _ => and_congr_right fun _ =>
        (mem_support_optionT_of_obs rfl).symm))

theorem mem_support_optionT_frequency {gs : List (Nat × (Unit → OptionT SPMF α))}
    (h : 0 < (gs.map Prod.fst).sum) {w : α} :
    some w ∈ SPMF.support (OptionT.run (frequency gs h))
      ↔ ∃ k g, (k, g) ∈ gs ∧ 0 < k ∧ some w ∈ SPMF.support (OptionT.run (g ())) := by
  refine (mem_support_optionT_of_obs (someObs.map_frequency gs h)).trans ?_
  simp only [Obs.select, WP.choose_bind_apply,
    Obs.selectD_map (fun v : WP Mix.angelic α => v (· = w)), List.map_map]
  refine (Mix.select_angelic _ (by simp [Function.comp_def]) h _).trans ?_
  constructor
  · rintro ⟨_, hp, hk, hw⟩
    obtain ⟨⟨k, g⟩, hmem, rfl⟩ := List.mem_map.mp hp
    exact ⟨k, g, hmem, hk, (mem_support_optionT_of_obs rfl).mpr hw⟩
  · rintro ⟨k, g, hmem, hk, hw⟩
    exact ⟨_, List.mem_map.mpr ⟨(k, g), hmem, rfl⟩, hk, (mem_support_optionT_of_obs rfl).mp hw⟩

/-! ## `someSupport` agrees with `support` on every *combinator*

Each of these is a one-liner from the lemmas above: the `Fail` interpretations differ (`⊥` at
`SPMF`, `pure none` at `OptionT SPMF`) but agree on `some`-values, and every other combinator is a
`bind`/`pure`/`choose` composite or a choice `someObs` reads. The corresponding statement for an
*opaque* `g : PGen α` is the free theorem `someSupport`'s docstring rules out. -/

section Combinators

variable {α β : Type}

@[simp] theorem someSupport_pure (a : α) : someSupport (pure a : PGen α) = (· = a) := by
  refine someSupport_ext fun x => ?_
  show some x ∈ SPMF.support (OptionT.run (Pure.pure a : OptionT SPMF α)) ↔ _
  rw [support_optionT_pure]
  simp

@[simp] theorem someSupport_empty : someSupport (PGen.empty : PGen α) = fun _ => False := by
  refine someSupport_ext fun x => ?_
  show some x ∈ SPMF.support ((OptionT.fail : OptionT SPMF α)) ↔ _
  simp [OptionT.fail, OptionT.mk, Pure.pure, SPMF.pure, SPMF.support, DFunLike.coe]

@[simp] theorem someSupport_bind {x : PGen α} {f : α → PGen β} :
    someSupport (x >>= f) = fun b => ∃ a, someSupport x a ∧ someSupport (f a) b := by
  refine someSupport_ext fun w => ?_
  show some w ∈ SPMF.support (OptionT.run (x.run >>= fun a => (f a).run : OptionT SPMF β)) ↔ _
  rw [mem_support_optionT_bind]
  rfl

@[simp] theorem someSupport_map {x : PGen α} {g : α → β} :
    someSupport (g <$> x) = fun b => ∃ a, someSupport x a ∧ g a = b := by
  refine someSupport_ext fun w => ?_
  show some w ∈ SPMF.support (OptionT.run (g <$> x.run : OptionT SPMF β)) ↔ _
  rw [mem_support_optionT_map]
  rfl

@[simp] theorem someSupport_pick {x y : PGen α} :
    someSupport (PGen.pick x y) = fun a => someSupport x a ∨ someSupport y a := by
  refine someSupport_ext fun w => ?_
  show some w ∈ SPMF.support (OptionT.run
      (oneOf [fun () => x.run, fun () => y.run] (by simp) : OptionT SPMF α)) ↔ _
  simp only [mem_support_optionT_oneOf, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left]
  rfl

@[simp] theorem someSupport_choose {lo hi : Nat} {h : lo ≤ hi} :
    someSupport (PGen.choose lo hi h) = fun a => lo ≤ a ∧ a ≤ hi := by
  refine someSupport_ext fun v => ?_
  show some v ∈ SPMF.support (OptionT.run (chooseNat lo hi h : OptionT SPMF Nat)) ↔ _
  rw [show (chooseNat lo hi h : OptionT SPMF Nat)
      = (·.down.val) <$> RandomChoice.choose lo hi h from rfl, mem_support_optionT_map]
  simp only [instRandomChoiceOptionT, mem_support_optionT_lift, SPMF.mem_support_choose_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, -, rfl⟩
    exact ha
  · intro hv
    exact ⟨⟨v, hv⟩, trivial, rfl⟩

@[simp] theorem someSupport_assume {b : Bool} {f : b → PGen α} :
    someSupport (PGen.assume b f) = fun a => ∃ h : b, someSupport (f h) a := by
  unfold PGen.assume
  split
  · next h => funext a; apply propext; exact ⟨fun hh => ⟨h, hh⟩, fun ⟨_, hh⟩ => hh⟩
  · next h =>
      funext a
      apply propext
      rw [someSupport_empty]
      exact ⟨False.elim, fun hh => absurd hh.1 h⟩

end Combinators

/-! ## `frequency` and `oneOf`

These are the combinators the **optimizer** actually emits — a `pick` chain is flattened into a
`frequency` so that a k-way choice is a function of its weights rather than of how the chain was
associated. -/

@[simp] theorem someSupport_frequency {α} {gs : List (Nat × PGen α)} (h) :
    someSupport (PGen.frequency gs h)
      = fun a => ∃ w g, (w, g) ∈ gs ∧ 0 < w ∧ someSupport g a := by
  refine someSupport_ext fun a => ?_
  simp only [PGen.totalize, PGen.frequency]
  rw [mem_support_optionT_frequency]
  exact PGen.Support.exists_mem_map_weighted
    (m := fun (g : PGen α) (_ : Unit) => (g.run : OptionT SPMF α))

@[simp] theorem someSupport_oneOf {α} {gs : List (PGen α)} (h) :
    someSupport (PGen.oneOf gs h) = fun a => ∃ g ∈ gs, someSupport g a := by
  funext a
  simp only [PGen.oneOf, someSupport_frequency, eq_iff_iff]
  exact PGen.Support.exists_mem_map_uniform

end Palamedes
