/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Data.Tree

/-!
# Spike: a *generic* `unfoldGo` through `partial_fixpoint`

The one go/no-go question for a generic unfold theory was: can `partial_fixpoint` accept an
anamorphism written **once**, over an abstract base functor, given Basalt's `Gen` class?
Answer: **yes**.

The recipe:
* abstract the base functor by a class providing a monadic traversal `mapM` of the recursive
  positions, *bundled with its monotonicity law*;
* export that law as a `@[partial_fixpoint_monotone]` lemma (one line); `partial_fixpoint`'s
  `monotonicity` tactic then closes the obligation for the generic definition via
  `monotone_bind` + that lemma;
* Basalt's `Gen` already carries the `Inhabited`/`CCPO`/`MonoBind` instances the fixpoint
  needs (this is what defeated the earlier generic-monad experiment in the prototype).

Each datatype's instance obligation closes with one **fixed, shape-independent** script:

```
cases t <;> repeat first | assumption | apply Lean.Order.monotone_apply _ _ hmono | monotonicity
```

It is *nearly* just `monotonicity` (the scoped `Lean.Order.monotonicity` tactic is public and
drives the same `@[partial_fixpoint_monotone]` lemma table), except for two gaps in the
standalone tactic, both by design rather than accident:

* it does not split `match`es — matcher-splitting lives in the `partial_fixpoint` *elaborator*,
  which generates specialized matcher-monotonicity lemmas on the fly; hence the leading
  `cases t`, which exposes each branch's plain `bind`/`pure` chain;
* `monotone_apply` (goals `monotone fun x => f x a`) is deliberately not a tagged lemma — its
  higher-order conclusion unifies with almost any `monotone` goal, so tagging it would derail
  the shared solver; inside real `partial_fixpoint` runs that shape is the recursive-call case,
  which the elaborator handles specially. Here `f` is our hypothesis instead, so the script
  supplies `monotone_apply _ _ hmono` as an explicit alternative.

Since the script does not mention the constructors, `derive_palamedes` can emit it verbatim for
any datatype; no per-shape proof generation is needed for this obligation.

This module is a witness, not (yet) library code: today's `derive_palamedes` emits concrete
per-type `unfoldGo`s. The generic route becomes load-bearing once `support_unfold` and the fusion
laws are proved once over this interface instead of once per type.
-/

namespace GenericUnfold

open Lean.Order Palamedes

/-- Monadic traversal of a base functor's recursive positions, bundled with the monotonicity law
`partial_fixpoint` needs. -/
class MTraversable (F : Type → Type) where
  mapM : ∀ {m : Type → Type} [Monad m] {β γ : Type}, (β → m γ) → F β → m (F γ)
  monotone_mapM : ∀ {m : Type → Type} [Monad m] [∀ α, Lean.Order.PartialOrder (m α)] [MonoBind m]
    {β γ : Type} {δ : Type} [Lean.Order.PartialOrder δ]
    (f : δ → β → m γ) (t : F β) (_ : monotone f),
    monotone (fun x => mapM (f x) t)

@[partial_fixpoint_monotone]
theorem monotone_mapMF {F : Type → Type} [MTraversable F]
    {m : Type → Type} [Monad m] [∀ α, Lean.Order.PartialOrder (m α)] [MonoBind m]
    {β γ δ : Type} [Lean.Order.PartialOrder δ]
    (f : δ → β → m γ) (t : F β) (hmono : monotone f) :
    monotone (fun x => MTraversable.mapM (f x) t) :=
  MTraversable.monotone_mapM f t hmono

/-- The "into" half of the initial algebra: rebuild `T` from one layer of `F T`. -/
class HasInto (T : Type) (F : Type → Type) where
  into : F T → T

/-- The generic anamorphism at any Basalt generator monad — written once, for every datatype.
`partial_fixpoint` discharges the monotonicity obligation through `monotone_mapMF`. -/
def unfoldGo {G : Type → Type} [Gen G] {F : Type → Type} [MTraversable F]
    {T β : Type} [HasInto T F]
    (step : β → G (F β)) (b : β) : G T :=
  step b >>= fun fb =>
    MTraversable.mapM (fun b' => unfoldGo step b') fb >>= fun ft =>
    pure (HasInto.into ft)
  partial_fixpoint

-- ── Instantiation at `Tree`, as the shape-check ─────────────────────────────

instance : MTraversable (TreeF α) where
  mapM f t :=
    match t with
    | .leaf => pure .leaf
    | .node l x r => do pure (.node (← f l) x (← f r))
  monotone_mapM f t hmono := by
    cases t <;> repeat
      first
      | assumption
      | apply Lean.Order.monotone_apply _ _ hmono
      | monotonicity

instance : HasInto (Palamedes.Tree α) (TreeF α) where
  into t :=
    match t with
    | .leaf => .leaf
    | .node l x r => .node l x r

/-- The generic unfold, specialized to `Tree` at the Palamedes carrier. -/
noncomputable def treeUnfold (f : β → PGen (TreeF α β)) (v : β) : PGen (Palamedes.Tree α) :=
  ⟨fun {_G} _ _ => unfoldGo (fun b => (f b).run) v⟩

#check @unfoldGo.eq_def  -- the fixpoint was accepted: its equation lemma exists

end GenericUnfold
