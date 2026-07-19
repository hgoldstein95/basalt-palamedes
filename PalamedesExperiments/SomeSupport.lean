import Palamedes.Data.List
import Palamedes.Data.Tree
import Palamedes.Failure

/-!
# Experiment: the `someSupport` twin of `X.support_unfold`

`someSupport g a := some a ∈ SPMF.support (totalize g)` — the values a *possibly-failing* generator
can actually produce, read through the `OptionT` interpretation instead of the `SPMF` one.

## What compiles here (no `sorry`)

* `someSupport_unfold` — the exact twin of `List.support_unfold`, by hand.
* `someSupport_tree_unfold` — the same for `Tree` (two recursive fields), by the *same* script.
* `support_optionT_pure`, `mem_support_optionT_bind`, `mem_support_optionT_lift` — a small,
  **datatype-independent** lemma kit; these are the only new lemmas the twins need.
* `someSupport_pure/empty/bind/pick/assume` — `someSupport C = support C` for each combinator.
* `someSupport_unfold_eq_support` — and it propagates through `unfold`.

## What does not (one annotated `sorry`)

* `parametricity : ∀ g, someSupport g = g.support` — a free theorem about `Gen.run`'s Π-type.

## Verdict

Middle option. The twin does need a *parallel induction* per datatype — it does **not** factor
through `List.support_unfold`, because that lemma's step is `(f d x).support` and there is no
`Palamedes.Gen` whose `support` is a given `someSupport`. But it does **not** need a second
130-line emitter either: the two proofs below are the emitted `genSupportUnfold` script with four
substitutions (`SPMF.support_bind` → `mem_support_optionT_bind`, `SPMF.support_pure` →
`support_optionT_pure`, `Set.mem_setOf_eq` → `Set.mem_singleton_iff`, and `injRef hw` →
`injRef (Option.some.inj hw)`), plus `some w ∈ … OptionT.run …` in the `show`. Parameterising
`genSupportUnfold` over that lemma kit and calling it twice is the cheap implementation.
-/

namespace Palamedes

open Lean.Order

/-- The support of a possibly-failing generator, read through `totalize`. -/
def someSupport (g : Gen α) : α → Prop :=
  fun a => some a ∈ SPMF.support (Gen.totalize g (G := SPMF))

/-- Sanity: `totalize` commutes with `unfold` definitionally. -/
example {α β} (f : Nat → β → Gen (ListF α β)) (b : β) (d₀ : Nat) :
    Gen.totalize (List.unfold f b d₀) (G := SPMF)
      = OptionT.run (List.unfoldGo (G := OptionT SPMF) (fun d x => (f d x).run) d₀ b) := rfl

section Helpers

variable {α β : Type}

theorem support_optionT_pure (a : α) :
    SPMF.support (OptionT.run (pure a : OptionT SPMF α)) = {some a} := by
  rw [show (pure a : OptionT SPMF α) = OptionT.mk (Pure.pure (some a)) from rfl]
  simp [OptionT.run, OptionT.mk]

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

end Helpers

/-! ## `someSupport` agrees with `support` on every *combinator*

Each of these is a one-liner from the two helper lemmas: the `Fail` interpretations differ (`⊥` at
`SPMF`, `pure none` at `OptionT SPMF`) but agree on `some`-values, and every other combinator is a
`bind`/`pure`/`choose` composite. What is *not* available is the corresponding statement for an
opaque `g : Gen α`: see `parametricity` at the bottom of the file. -/

section Combinators

variable {α β : Type}

@[simp] theorem someSupport_pure (a : α) : someSupport (pure a : Gen α) = (· = a) := by
  funext x
  apply propext
  show some x ∈ SPMF.support (OptionT.run (Pure.pure a : OptionT SPMF α)) ↔ _
  rw [support_optionT_pure]
  simp

@[simp] theorem someSupport_empty : someSupport (Gen.empty : Gen α) = fun _ => False := by
  funext x
  apply propext
  show some x ∈ SPMF.support ((OptionT.fail : OptionT SPMF α)) ↔ _
  simp [OptionT.fail, OptionT.mk, Pure.pure, SPMF.pure, SPMF.support, DFunLike.coe]

@[simp] theorem someSupport_bind {x : Gen α} {f : α → Gen β} :
    someSupport (x >>= f) = fun b => ∃ a, someSupport x a ∧ someSupport (f a) b := by
  funext w
  apply propext
  show some w ∈ SPMF.support (OptionT.run (x.run >>= fun a => (f a).run : OptionT SPMF β)) ↔ _
  rw [mem_support_optionT_bind]
  rfl

@[simp] theorem someSupport_pick {x y : Gen α} :
    someSupport (Gen.pick x y) = fun a => someSupport x a ∨ someSupport y a := by
  funext w
  apply propext
  show some w ∈ SPMF.support (OptionT.run
      (RandomChoice.pick (fun () => x.run) (fun () => y.run) : OptionT SPMF α))
    ↔ (some w ∈ SPMF.support (OptionT.run (x.run : OptionT SPMF α))
        ∨ some w ∈ SPMF.support (OptionT.run (y.run : OptionT SPMF α)))
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

@[simp] theorem someSupport_assume {b : Bool} {f : b → Gen α} :
    someSupport (Gen.assume b f) = fun a => ∃ h : b, someSupport (f h) a := by
  unfold Gen.assume
  split
  · next h => funext a; apply propext; exact ⟨fun hh => ⟨h, hh⟩, fun ⟨_, hh⟩ => hh⟩
  · next h =>
      funext a
      apply propext
      rw [someSupport_empty]
      exact ⟨False.elim, fun hh => absurd hh.1 h⟩

end Combinators

section Main

variable {α β : Type}

theorem someSupport_unfold {f : Nat → β → Gen (ListF α β)} {b : β} {d₀ : Nat} :
    someSupport (List.unfold f b d₀)
      = List.unfold_support (fun d x => someSupport (f d x)) d₀ b := by
  funext w
  apply propext
  show some w ∈ SPMF.support
      (OptionT.run (List.unfoldGo (G := OptionT SPMF) (fun d x => (f d x).run) d₀ b))
    ↔ List.unfold_support (fun d x => someSupport (f d x)) d₀ b w
  induction w generalizing b d₀ with
  | nil =>
    unfold List.unfoldGo
    rw [mem_support_optionT_bind]
    simp only [List.unfold_support]
    constructor
    · rintro ⟨tv, ht, hw⟩
      cases tv with
      | nil => exact ht
      | cons y1 y2 =>
        simp only [mem_support_optionT_bind, support_optionT_pure,
          Set.mem_singleton_iff] at hw <;> simp_all
    · intro h
      exact ⟨.nil, h, by rw [support_optionT_pure]; simp⟩
  | cons a t ih =>
    unfold List.unfoldGo
    rw [mem_support_optionT_bind]
    simp only [List.unfold_support]
    constructor
    · rintro ⟨tv, ht, hw⟩
      cases tv with
      | nil =>
        simp only [support_optionT_pure, Set.mem_singleton_iff] at hw <;> simp_all
      | cons y1 y2 =>
        simp only [mem_support_optionT_bind, support_optionT_pure,
          Set.mem_singleton_iff] at hw
        obtain ⟨v1, hv1, heq⟩ := hw
        obtain ⟨rfl, rfl⟩ := List.cons.inj (Option.some.inj (Eq.symm heq))
        exact ⟨y2, ht, (ih).mp hv1⟩
    · rintro ⟨b1, hb, h1⟩
      refine ⟨.cons a b1, hb, ?_⟩
      rw [mem_support_optionT_bind]
      exact ⟨t, ih.mpr h1, by rw [support_optionT_pure]; simp⟩

/-- The twin theorem is exactly the *inductive step* of "`someSupport` = `support`" at the
recursion: given the equation for the step, it propagates through the unfold. -/
theorem someSupport_unfold_eq_support {f : Nat → β → Gen (ListF α β)} {b : β} {d₀ : Nat}
    (h : ∀ d x, someSupport (f d x) = Gen.support (f d x)) :
    someSupport (List.unfold f b d₀) = Gen.support (List.unfold f b d₀) := by
  rw [someSupport_unfold, List.support_unfold]
  congr 1
  funext d x
  exact h d x

end Main

/-! ## Second datatype: the same script shape works for a *branching* type

`Tree` is the load-bearing shape check: two recursive fields, hence two IHs and a nested
`bind`-chain in the `node` case. The proof below is the *same* script as `someSupport_unfold`
modulo constructor arity — which is exactly what `genSupportUnfold` already abstracts over. -/

section TreeTwin

variable {α β : Type}

theorem someSupport_tree_unfold {f : Nat → β → Gen (TreeF α β)} {b : β} {d₀ : Nat} :
    someSupport (Tree.unfold f b d₀)
      = Tree.unfold_support (fun d x => someSupport (f d x)) d₀ b := by
  funext w
  apply propext
  show some w ∈ SPMF.support
      (OptionT.run (Tree.unfoldGo (G := OptionT SPMF) (fun d x => (f d x).run) d₀ b))
    ↔ Tree.unfold_support (fun d x => someSupport (f d x)) d₀ b w
  induction w generalizing b d₀ with
  | leaf =>
    unfold Tree.unfoldGo
    rw [mem_support_optionT_bind]
    simp only [Tree.unfold_support]
    constructor
    · rintro ⟨tv, ht, hw⟩
      cases tv with
      | leaf => exact ht
      | node y1 y2 y3 =>
        simp only [mem_support_optionT_bind, support_optionT_pure,
          Set.mem_singleton_iff] at hw <;> simp_all
    · intro h
      exact ⟨.leaf, h, by rw [support_optionT_pure]; simp⟩
  | node l x r ih1 ih2 =>
    unfold Tree.unfoldGo
    rw [mem_support_optionT_bind]
    simp only [Tree.unfold_support]
    constructor
    · rintro ⟨tv, ht, hw⟩
      cases tv with
      | leaf =>
        simp only [support_optionT_pure, Set.mem_singleton_iff] at hw <;> simp_all
      | node y1 y2 y3 =>
        simp only [mem_support_optionT_bind, support_optionT_pure,
          Set.mem_singleton_iff] at hw
        obtain ⟨v1, hv1, v2, hv2, heq⟩ := hw
        obtain ⟨rfl, rfl, rfl⟩ := Tree.node.inj (Option.some.inj (Eq.symm heq))
        exact ⟨y1, y3, ht, ih1.mp hv1, ih2.mp hv2⟩
    · rintro ⟨b1, b2, hb, h1, h2⟩
      refine ⟨.node b1 x b2, hb, ?_⟩
      rw [mem_support_optionT_bind]
      refine ⟨l, ih1.mpr h1, ?_⟩
      rw [mem_support_optionT_bind]
      exact ⟨r, ih2.mpr h2, by rw [support_optionT_pure]; simp⟩

end TreeTwin

/-! ## The obstruction to the *cheap* route

Every combinator lemma above says `someSupport C = support C` for `C` a concrete combinator, and
`someSupport_unfold_eq_support` says the same propagates through `unfold`. So the global statement

  `∀ (g : Gen α), someSupport g = g.support`

holds for every generator that is *built* from the combinator basis — but `Gen` is a `structure`
wrapping an opaque polymorphic function, not an inductive syntax, so there is no induction principle
to run that argument over. The goal below is the free theorem for `Gen.run`; nothing in Lean's
logic proves it. -/

/-- **Not provable.** `g.run` is an arbitrary element of `∀ {G} [Gen G] [Fail G], G α`; relating its
`SPMF` instance to its `OptionT SPMF` instance is a parametricity (free-theorem) statement about
that Π-type. Lean's logic is compatible with non-parametric inhabitants (there is no internal
relational interpretation available), so this needs *either* a parametricity axiom *or* replacing
`Gen`'s carrier by an inductive syntax of generators (with the combinator lemmas above as its
cases). Difficulty: not a proof-engineering problem, a foundational one. -/
theorem parametricity (g : Gen α) : someSupport g = g.support := by
  sorry

#print axioms Palamedes.someSupport_unfold
#print axioms Palamedes.someSupport_tree_unfold

end Palamedes
