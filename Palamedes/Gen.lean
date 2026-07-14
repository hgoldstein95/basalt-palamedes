/-
Copyright (c) 2025 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Basalt

/-!
# Palamedes generators, on top of Basalt

A Palamedes `Gen α` wraps a *polymorphic Basalt generator*: a term usable at any generator monad `G`
(i.e. any `_root_.Gen G`, Basalt's generator typeclass) that *additionally* supports failure
(`Fail G`). The wrapped term, `g.run`, is the bare Basalt generator; it can be instantiated at `SPMF`
for proofs or `Plausible.Gen` for sampling. Synthesis builds these `Gen` terms as data; a generator
acquires meaning only by *interpreting* its `run` at a chosen `G`. The proof interpretation is Basalt's
sub-probability mass function (`SPMF`), so `support` is `SPMF.support`.

## Failure as a capability (`Fail`)

Filtering (`assume`/`empty`) needs a notion of *failure*. We make that an explicit capability `Fail`
rather than reusing Basalt's CCPO bottom (`Lean.Order.bot`) for two reasons:

* **Computability.** `Lean.Order.bot` is the supremum of the empty chain, defined via
  `Classical.choose`, so it is `noncomputable` *even when the underlying CCPO has a perfectly
  computable bottom* (e.g. `Except.error default` for `Plausible.Gen`). Routing failure through a
  `Fail.fail` method lets each interpretation supply its own computable failure.
* **Totality.** A generator that never fails is exactly one definable *without* the `Fail`
  capability. Splitting `Fail` out of the base `Gen` class makes "assume-free" a structural fact: see
  `TGen` below and `Palamedes.Gen.total`.

Because Basalt already owns the name `Gen` (its generator typeclass, at the root namespace), the
Palamedes carrier lives under `namespace Palamedes`; we refer to Basalt's class as `_root_.Gen`.
-/

namespace Palamedes

open Lean.Order

/-- The failure capability: a generator monad with a designated "produces nothing" element. This is
deliberately *separate* from Basalt's base `Gen` class so that generators which never fail can be
typed without it (see `TGen`). For `SPMF` the failure is the bottom distribution `⊥` (mass 0); for an
executable interpretation it is a generation failure / local backtracking point. -/
class Fail (G : Type → Type) where
  fail : ∀ {α}, G α

/-- A Palamedes generator wraps a Basalt generator that is polymorphic over the choice of generator
monad — any `_root_.Gen G` that also supports failure (`Fail G`). `g.run` is the underlying Basalt
generator. -/
structure Gen (α : Type) : Type 1 where
  run : ∀ {G : Type → Type} [_root_.Gen G] [Fail G], G α

/-- A *failure-free* Palamedes generator: polymorphic over every `_root_.Gen G`, with **no** `Fail`
requirement. A `TGen` cannot mention `assume`/`empty`, so it is "assume-free" by construction. It
coerces into `Gen` (forgetting that it never needed `Fail`); `Palamedes.Gen.total` is defined as
"factors through a `TGen`." -/
structure TGen (α : Type) : Type 1 where
  run : ∀ {G : Type → Type} [_root_.Gen G], G α

/-- Forget that a failure-free generator never needed `Fail`, viewing it as a `Gen`. -/
def TGen.toGen (t : TGen α) : Gen α := ⟨fun {_G} _ _ => t.run⟩

namespace Gen

@[ext] theorem ext {x y : Gen α} (h : ∀ {G} [_root_.Gen G] [Fail G], x.run = (y.run : G α)) : x = y := by
  cases x; cases y; congr; funext G inst finst; exact h

protected def pure (a : α) : Gen α := ⟨fun {_G} _ _ => Pure.pure a⟩

protected def bind (x : Gen α) (f : α → Gen β) : Gen β :=
  ⟨fun {_G} _ _ => x.run >>= fun a => (f a).run⟩

instance : Pure Gen where pure := Gen.pure
instance : Bind Gen where bind := Gen.bind
instance : Monad Gen where

/-- Uniform binary choice. -/
def pick (x y : Gen α) : Gen α :=
  ⟨fun {_G} _ _ => RandomChoice.pick (fun () => x.run) (fun () => y.run)⟩

/-- Weighted n-ary choice. Branch `(wⱼ, gⱼ)` is selected with probability `wⱼ / Σw`. The optimizer
flattens `pick` chains into `frequency` so that a k-way choice is a function of the weights rather
than of how the chain was associated. -/
def frequency (gs : List (Nat × Gen α)) (h : 0 < (gs.map Prod.fst).sum := by simp) : Gen α :=
  ⟨fun {_G} _ _ =>
    _root_.frequency (gs.map fun p => (p.1, fun _ => p.2.run))
      (by simpa [List.map_map, Function.comp_def] using h)⟩

/-- Uniform n-ary choice: `frequency` with all weights 1. -/
def oneOf (gs : List (Gen α)) (h : gs ≠ [] := by simp) : Gen α :=
  frequency (gs.map fun g => (1, g)) (by cases gs <;> simp_all)

section Delab

open Lean PrettyPrinter Delaborator SubExpr

/-! The side-condition arguments of `frequency`/`oneOf` are autoParams (`by simp`), so an
application that omits them still elaborates whenever `simp` can discharge the condition. The
delaborators below therefore drop the argument in that case rather than rendering it. -/

@[app_delab Palamedes.Gen.oneOf]
def delabOneOf : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity ``Palamedes.Gen.oneOf 3
  guard <| (e.getArg! 1).isAppOf ``List.cons
  let gs ← withNaryArg 1 delab
  let fn := mkIdent (← unresolveNameGlobal ``Palamedes.Gen.oneOf)
  `($fn $gs)

def natLit? (e : Expr) : Option Nat :=
  match e.nat? with
  | some n => some n
  | none => match_expr e with
    | OfNat.ofNat _ n _ => n.nat?
    | _ => none

/-- Is `w` positive for *every* value of the variables in it, by inspection? A positive numeral, a
sum with a positive summand, or a product of positives. Weights are not always closed: the affine
schedules `a + b * d` that `installWeights` emits mention the recursion's depth, so a delaborator
that could only add up numerals would give up on precisely the generators that need weights. -/
private partial def weightPos (w : Expr) : Bool :=
  match natLit? w with
  | some n => 0 < n
  | none =>
    match_expr w with
    | HAdd.hAdd _ _ _ _ x y => weightPos x || weightPos y
    | HMul.hMul _ _ _ _ x y => weightPos x && weightPos y
    | _ => false

/-- Does `l` have a branch whose weight is positive by inspection? Then `0 < Σw`, which is what the
autoParam has to re-derive, so the proof can be dropped. -/
private partial def someWeightPos (l : Expr) : Bool :=
  match_expr l with
  | List.cons _ hd tl =>
    (match_expr hd with
      | Prod.mk _ _ w _ => weightPos w
      | _ => false) || someWeightPos tl
  | _ => false

@[app_delab Palamedes.Gen.frequency]
def delabFrequency : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity ``Palamedes.Gen.frequency 3
  guard <| someWeightPos (e.getArg! 1)
  let gs ← withNaryArg 1 delab
  let fn := mkIdent (← unresolveNameGlobal ``Palamedes.Gen.frequency)
  `($fn $gs)

end Delab

/-- The empty generator: produces nothing. It is the `Fail` capability's `fail`; in `SPMF` that is
`⊥` (mass 0), and in an executable interpretation it is a generation failure, which is what makes
`assume`'s `else` branch act as a local backtracking point. It is computable whenever the chosen
interpretation's `Fail` instance is. -/
def empty : Gen α := ⟨fun {_G} _ _ => Fail.fail⟩

/-- A guarded generator: `f` when `b` holds, `empty` otherwise — so the failing branch contributes
nothing to the support. This is how a `Bool`-valued side condition is woven into a generator.

Operationally it is a *filter*, not a backtracking point: the sampler has no backtracking, so a
failing `assume` throws (`Palamedes/Sample.lean`). An `assume` the optimizer could not discharge is
therefore a real filter, which is what `allow_partial` exists to permit. -/
def assume (b : Bool) (f : b → Gen α) : Gen α :=
  if h : b then f h else empty

/-! ## Recursion

Recursion is *not* a single core combinator. Following Basalt, each recursive datatype defines its
own `unfold` operator as a direct `partial_fixpoint` over Basalt's CCPO, along with its own `support`
lemma and totality proof. `derive_palamedes` emits all of that per datatype (see
`Palamedes/Derive.lean`); `Palamedes/Data/` just invokes it. -/

/-! ## The `SPMF` interpretation

`support` interprets a generator at `SPMF`. That needs a `Fail SPMF` instance; failure is the bottom
distribution. It is `noncomputable`, but `SPMF` is the proof-only interpretation, so that is fine. -/

noncomputable instance : Fail SPMF := ⟨Lean.Order.bot⟩

/-! ## Support

`support g` is the set of values `g` can produce, computed via the `SPMF` interpretation. -/

/-- The set of values a generator can produce, via its `SPMF` interpretation. -/
def support (g : Gen α) : α → Prop := SPMF.support g.run

namespace Support

/-- The `SPMF` interpretation of `empty` is the bottom distribution, whose support is empty. -/
theorem support_bot : SPMF.support (Lean.Order.bot : SPMF α) = (∅ : Set α) := by
  ext a
  rw [show (Lean.Order.bot : SPMF α) = CCPO.csup (chain_empty (SPMF α)) from rfl,
    SPMF.mem_support_csup]
  simp [empty_chain]

@[simp]
theorem support_pure :
    support (pure a) = (· = a) := by
  funext x
  simp only [support, Pure.pure, Gen.pure, eq_iff_iff]
  show x ∈ SPMF.support (Pure.pure a) ↔ x = a
  simp

@[simp]
theorem support_bind :
    support (x >>= f) = fun b => ∃ a, support x a ∧ support (f a) b := by
  funext b
  apply propext
  show b ∈ SPMF.support (x.run >>= fun a => (f a).run) ↔ _
  simp only [SPMF.support_bind, Set.mem_setOf_eq]
  rfl

@[simp]
theorem support_pick :
    support (pick x y) = fun a => support x a ∨ support y a := by
  funext a
  apply propext
  show a ∈ SPMF.support (RandomChoice.pick (fun () => x.run) (fun () => y.run)) ↔ _
  simp only [SPMF.support_pick, Set.mem_union]
  rfl

@[simp]
theorem support_frequency {gs : List (Nat × Gen α)} (h) :
    support (frequency gs h) = fun a => ∃ w g, (w, g) ∈ gs ∧ 0 < w ∧ support g a := by
  funext a
  apply propext
  show a ∈ SPMF.support (_root_.frequency (gs.map fun p => (p.1, fun _ => p.2.run))
      (by simpa [List.map_map, Function.comp_def] using h)) ↔ _
  rw [SPMF.support_frequency]
  simp only [Set.mem_setOf_eq, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨w, g, ⟨⟨w', g'⟩, hmem, hw', hg'⟩, hw, ha⟩
    subst hw'
    subst hg'
    exact ⟨w', g', hmem, hw, ha⟩
  · rintro ⟨w, g, hmem, hw, ha⟩
    exact ⟨w, fun _ => g.run, ⟨⟨w, g⟩, hmem, rfl, rfl⟩, hw, ha⟩

@[simp]
theorem support_oneOf {gs : List (Gen α)} (h) :
    support (oneOf gs h) = fun a => ∃ g ∈ gs, support g a := by
  funext a
  simp only [oneOf, support_frequency, List.mem_map, eq_iff_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨w, g, ⟨g', hmem, hw, hg⟩, _, ha⟩
    subst hg
    exact ⟨g', hmem, ha⟩
  · rintro ⟨g, hmem, ha⟩
    exact ⟨1, g, ⟨g, hmem, rfl, rfl⟩, Nat.one_pos, ha⟩

@[simp]
theorem support_empty :
    support (empty : Gen α) = fun _ => False := by
  funext a
  simp only [support, empty, eq_iff_iff, iff_false]
  show a ∉ SPMF.support (Fail.fail : SPMF α)
  rw [show (Fail.fail : SPMF α) = Lean.Order.bot from rfl, support_bot]
  simp

@[simp]
theorem support_assume :
    support (assume b f) = fun a => ∃ h : b, support (f h) a := by
  funext a
  simp only [assume]
  by_cases h : b <;> simp_all [support_empty]

@[simp]
theorem support_map :
    support (f <$> x) = fun b => ∃ a, support x a ∧ b = f a := by
  funext b
  apply propext
  show b ∈ SPMF.support (x.run >>= fun a => Pure.pure (f a)) ↔ _
  simp only [SPMF.support_bind, SPMF.support_pure, Set.mem_setOf_eq, Set.mem_singleton_iff]
  rfl

end Support

end Gen

end Palamedes

notation v " ∈ " "〚" g "〛" => Palamedes.Gen.support g v
