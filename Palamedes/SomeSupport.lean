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

open Palamedes.PGen Helpers

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

/-- The `pick` lemma. `pick` is `choose 0 1 >>= …`, so this follows from the `bind` lemma once the
two-element index is case-split — but stating it separately is what lets the *primitive* generators'
`someSupport` proofs mirror their `PGen.support` scripts line for line. -/
theorem mem_support_optionT_pick {x y : OptionT SPMF α} {w : α} :
    some w ∈ SPMF.support (OptionT.run
        (RandomChoice.pick (fun () => x) (fun () => y) : OptionT SPMF α))
      ↔ some w ∈ SPMF.support (OptionT.run x) ∨ some w ∈ SPMF.support (OptionT.run y) := by
  simp only [RandomChoice.pick, instRandomChoiceOptionT]
  rw [mem_support_optionT_bind]
  constructor
  · rintro ⟨n, hn, hw⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp n.down.property.2 with h0 | h1
    · left; simpa [h0] using hw
    · right; simpa [h1] using hw
  · intro h
    cases h with
    | inl hx => exact ⟨⟨⟨0, by omega⟩⟩, by simp, by simpa using hx⟩
    | inr hy => exact ⟨⟨⟨1, by omega⟩⟩, by simp, by simpa using hy⟩

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

/-! ## `someSupport` agrees with `support` on every *combinator*

Each of these is a one-liner from the two helper lemmas: the `Fail` interpretations differ (`⊥` at
`SPMF`, `pure none` at `OptionT SPMF`) but agree on `some`-values, and every other combinator is a
`bind`/`pure`/`choose` composite. The corresponding statement for an *opaque* `g : PGen α` is the
free theorem `someSupport`'s docstring rules out. -/

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
      (RandomChoice.pick (fun () => x.run) (fun () => y.run) : OptionT SPMF α))
    ↔ (some w ∈ SPMF.support (OptionT.run (x.run : OptionT SPMF α))
        ∨ some w ∈ SPMF.support (OptionT.run (y.run : OptionT SPMF α)))
  exact mem_support_optionT_pick

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
associated. `OptionT.run` does not distribute over `frequency` unconditionally; `run_frequencyAux`
has the `0 < total` hypothesis that makes it true. -/


theorem run_frequencySelect {α} (gs : List (Nat × (Unit → OptionT SPMF α))) (n : Nat) (h) :
    OptionT.run (frequencySelect gs n h)
      = frequencySelect (gs.map fun p => (p.1, fun _ => OptionT.run (p.2 ()))) n
          (by simpa [List.map_map, Function.comp_def] using h) := by
  induction gs generalizing n with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨k, x⟩ := g
    simp only [frequencySelect, List.map_cons]
    split <;> simp_all

theorem run_lift_bind {α β} (p : SPMF α) (k : α → OptionT SPMF β) :
    OptionT.run (OptionT.lift p >>= k) = p >>= fun a => OptionT.run (k a) := by
  simp only [OptionT.lift, OptionT.mk, OptionT.run, bind, OptionT.bind]
  rw [SPMF.bind_assoc]
  congr 1
  funext a
  show (SPMF.pure (some a)).bind _ = _
  rw [SPMF.pure_bind]

theorem run_map_lift {α β} (p : SPMF α) (g : α → β) :
    OptionT.run (g <$> (OptionT.lift p) : OptionT SPMF β)
      = OptionT.run (OptionT.lift (g <$> p) : OptionT SPMF β) := by
  show OptionT.run (OptionT.lift p >>= fun a => pure (g a)) = _
  rw [run_lift_bind]
  show SPMF.bind p (fun a => SPMF.pure (some (g a)))
    = SPMF.bind (SPMF.bind p (fun a => SPMF.pure (g a))) _
  rw [SPMF.bind_assoc]
  congr 1
  funext a
  rw [SPMF.pure_bind]
  rfl

theorem run_lift_map_bind {γ δ α} (p : SPMF γ) (g : γ → δ) (k : δ → OptionT SPMF α) :
    OptionT.run ((g <$> OptionT.lift p : OptionT SPMF δ) >>= k)
      = SPMF.bind (g <$> p) (fun d => OptionT.run (k d)) := by
  rw [show (g <$> OptionT.lift p : OptionT SPMF δ) = OptionT.lift (g <$> p) from
    OptionT.ext (run_map_lift _ _)]
  exact run_lift_bind _ _

/-- `frequencyAux`'s `else default` branch is unreachable: the index is drawn from
`[0, total-1]`, so `¬ n < total` contradicts `0 < total`. That matters here because the two
`default`s are *not* the same term — `OptionT SPMF α`'s `Inhabited` is `pure none` while
`SPMF (Option α)`'s is its own — so the equation would be false without the bound. -/
theorem run_frequencyAux {α} (gs : List (Nat × (Unit → OptionT SPMF α)))
    (total : Nat) (htpos : 0 < total) (ht) (ht') :
    OptionT.run (frequencyAux gs total ht)
      = frequencyAux (gs.map fun p => (p.1, fun _ => OptionT.run (p.2 ()))) total ht' := by
  simp only [frequencyAux]
  rw [show (RandomChoice.choose 0 (total - 1) (Nat.zero_le _) : OptionT SPMF _)
      = OptionT.lift (RandomChoice.choose 0 (total - 1) (Nat.zero_le _)) from rfl]
  rw [run_lift_map_bind]
  congr 1
  funext n
  obtain ⟨hn0, hn1⟩ := n.property
  split
  · exact run_frequencySelect _ _ _
  · omega

theorem run_frequency {α} (gs : List (Nat × (Unit → OptionT SPMF α))) (h) :
    OptionT.run (frequency gs h)
      = frequency (gs.map fun p => (p.1, fun _ => OptionT.run (p.2 ())))
          (by simpa [List.map_map, Function.comp_def] using h) := by
  have hfst : (List.map Prod.fst (gs.map fun p : Nat × (Unit → OptionT SPMF α) =>
        ((p.1 : Nat), fun _ : Unit => OptionT.run (p.2 ()))) : List Nat)
      = List.map Prod.fst gs := by simp [List.map_map, Function.comp_def]
  show OptionT.run (frequencyAux gs _ rfl) = frequencyAux _ _ rfl
  simp only [hfst]
  exact run_frequencyAux _ _ h _ _

@[simp] theorem someSupport_frequency {α} {gs : List (Nat × PGen α)} (h) :
    someSupport (PGen.frequency gs h)
      = fun a => ∃ w g, (w, g) ∈ gs ∧ 0 < w ∧ someSupport g a := by
  refine someSupport_ext fun a => ?_
  show some a ∈ SPMF.support _ ↔ _
  rw [show PGen.totalize (PGen.frequency gs h) (G := SPMF)
      = OptionT.run (_root_.frequency (gs.map fun p => (p.1, fun _ => p.2.run))
          (by simpa [List.map_map, Function.comp_def] using h) : OptionT SPMF α) from rfl]
  rw [run_frequency, SPMF.support_frequency]
  simp only [Set.mem_setOf_eq, List.map_map, Function.comp_def]
  exact PGen.Support.exists_mem_map_weighted
    (m := fun (g : PGen α) (_ : Unit) => OptionT.run (g.run : OptionT SPMF α))

@[simp] theorem someSupport_oneOf {α} {gs : List (PGen α)} (h) :
    someSupport (PGen.oneOf gs h) = fun a => ∃ g ∈ gs, someSupport g a := by
  funext a
  simp only [PGen.oneOf, someSupport_frequency, eq_iff_iff]
  exact PGen.Support.exists_mem_map_uniform

end Palamedes
