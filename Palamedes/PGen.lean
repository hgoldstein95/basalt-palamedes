/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/
import Basalt

/-!
# Palamedes Generators

A Palamedes `PGen α` wraps a polymorphic Basalt generator that additionally supports failure (`Fail
G`). The wrapped term, `g.run`, is the bare Basalt generator; it can be instantiated at `SPMF` for
proofs or `Plausible.Gen` for sampling. Synthesis builds these `PGen` terms as data; a generator
acquires meaning only by interpreting its `run` at a chosen `G`. The proof interpretation is
Basalt's sub-probability mass function (`SPMF`), so `support` is `SPMF.support`.

## Failure

Filtering (`assume`/`empty`) needs a notion of *failure*. We make that an explicit capability `Fail`
rather than reusing Basalt's CCPO bottom (`Lean.Order.bot`) for two reasons:

* **Computability.** `Lean.Order.bot` is the supremum of the empty chain, defined via
  `Classical.choose`, so it is `noncomputable`. (Even worse, in some interpretations
  `Lean.Order.bot` corresponds to divergence.) Routing failure through a `Fail.fail` method lets
  each interpretation supply its own computable failure.
* **Totality.** We explicitly try to remove all failures from generators during optimization.
  If our optimizer is able to produce a generator that typechecks without `Fail`, we are guaranteed
  that this failure has been removed.
-/

namespace Palamedes

open Lean.Order

/-- The failure capability: a generator monad with a designated "produces nothing" element. -/
class Fail (G : Type → Type) where
  fail : ∀ {α}, G α

/-- A Palamedes generator wraps a Basalt generator that also supports failure. -/
structure PGen (α : Type) : Type 1 where
  run : ∀ {G : Type → Type} [Gen G] [Fail G], G α

/-- A failure-free Palamedes generator. -/
structure TGen (α : Type) : Type 1 where
  run : ∀ {G : Type → Type} [Gen G], G α

/-- Forget that a failure-free generator never needed `Fail`, viewing it as a `PGen`. -/
def TGen.toGen (t : TGen α) : PGen α := ⟨fun {_G} _ _ => t.run⟩

namespace PGen

@[ext] theorem ext {x y : PGen α} (h : ∀ {G} [Gen G] [Fail G], x.run = (y.run : G α)) : x = y := by
  cases x; cases y; congr; funext G inst finst; exact h

protected def pure (a : α) : PGen α := ⟨fun {_G} _ _ => Pure.pure a⟩

protected def bind (x : PGen α) (f : α → PGen β) : PGen β :=
  ⟨fun {_G} _ _ => x.run >>= fun a => (f a).run⟩

instance : Pure PGen where pure := PGen.pure
instance : Bind PGen where bind := PGen.bind
instance : Monad PGen where

/-- Uniform binary choice. -/
def pick (x y : PGen α) : PGen α :=
  ⟨fun {_G} _ _ => RandomChoice.pick (fun () => x.run) (fun () => y.run)⟩

/-- Weighted n-ary choice. Branch `(wⱼ, gⱼ)` is selected with probability `wⱼ / Σw`. -/
def frequency (gs : List (Nat × PGen α)) (h : 0 < (gs.map Prod.fst).sum := by simp) : PGen α :=
  ⟨fun {_G} _ _ =>
    _root_.frequency (gs.map fun p => (p.1, fun _ => p.2.run))
      (by simpa [List.map_map, Function.comp_def] using h)⟩

/-- Uniform n-ary choice. -/
def oneOf (gs : List (PGen α)) (h : gs ≠ [] := by simp) : PGen α :=
  frequency (gs.map fun g => (1, g)) (by cases gs <;> simp_all)

section Delab

open Lean PrettyPrinter Delaborator SubExpr

/-! ## Delaborator Hacks

Choice combinators like `oneOf` and `frequency` carry a side conditions (`gs ≠ []`, `0 < Σ weights`)
as an explicit argument. By default, these either print as `⋯`, which makes the generator unusable;
if we set `pp.proofs := true`, those proofs become an ugly wall of text. To get around these issues,
we hack the delaborator to only print the proofs when they can't be easily reconstructed by the
combinator's autoparam.

The same problem, and the same fix, applies to a *primitive* whose side condition is an ordinary
explicit argument — `choose`'s `lo ≤ hi`, `elements`' `xs.length > 0`. Those live in `Data/`, so
`delabDroppingProof` and `gen_side_condition` below are the shared pieces they register against;
`delabDroppingSideCondition` stays private because the three combinators it serves are all here. -/

/-- Discharge a generator primitive's side condition, for its `autoParam`.

Two cases, and a primitive's delaborator drops the proof exactly when one of them will fire on the
pasted term: the condition holds outright (literal bounds, a literal branch list), or it follows
from a decidable guard already in context — which is the shape a floated `assume` leaves, since the
optimizer turns it into a `dite` binding `decide P = true`.

Each branch is `done`-terminated, so a branch that makes progress without closing the goal falls
through to the next rather than committing. `elements`' condition is where that bites: `simp` turns
`(Γ.idxsOf τ).length > 0` into `τ ∈ Γ` and stops, which is progress, and the guard in context is
about the length. -/
syntax "gen_side_condition" : tactic
macro_rules
  | `(tactic| gen_side_condition) =>
    `(tactic| first
        | (simp; done)
        | (simp_all only [decide_eq_true_eq]; done)
        | (simp_all; done))

def natLit? (e : Expr) : Option Nat :=
  match e.nat? with
  | some n => some n
  | none => match_expr e with
    | OfNat.ofNat _ n _ => n.nat?
    | _ => none

/-- Is `w` positive for every value of the variables in it, by inspection?

This is a rough heuristic that captures literal affine expressions like `2 + 3 * d` as well as
`Tuning.weight θ i d`. -/
private partial def weightPos (w : Expr) : Bool :=
  match natLit? w with
  | some n => 0 < n
  | none =>
    match_expr w with
    | HAdd.hAdd _ _ _ _ x y => weightPos x || weightPos y
    | HMul.hMul _ _ _ _ x y => weightPos x && weightPos y
    | Tuning.weight _ _ _ => true
    | _ => false

/-- Does `l` have a branch whose weight is positive by inspection? -/
private partial def someWeightPos (l : Expr) : Bool :=
  match_expr l with
  | List.cons _ hd tl =>
    (match_expr hd with
      | Prod.mk _ _ w _ => weightPos w
      | _ => false) || someWeightPos tl
  | _ => false

/-- Render `c gs`, dropping `c`'s trailing side-condition argument, when `branchesOk` says the branch
list at `gsIdx` makes that side condition recoverable. -/
private def delabDroppingSideCondition
    (c : Name) (arity gsIdx : Nat)
    (branchesOk : Expr → Bool) :
    Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity c arity
  guard <| branchesOk (e.getArg! gsIdx)
  let gs ← withNaryArg gsIdx delab
  let fn := mkIdent (← unresolveNameGlobal c)
  `($fn $gs)

@[app_delab Palamedes.PGen.oneOf]
def delabOneOf : Delab :=
  delabDroppingSideCondition ``Palamedes.PGen.oneOf 3 1 (·.isAppOf ``List.cons)

@[app_delab Palamedes.PGen.frequency]
def delabFrequency : Delab :=
  delabDroppingSideCondition ``Palamedes.PGen.frequency 3 1 someWeightPos

-- `_root_`-qualified: this section is inside `namespace Palamedes.PGen`, where a bare `frequency`
-- resolves to the carrier's combinator. Unqualified, this silently registers a *second* delaborator
-- for `PGen.frequency` and Basalt's keeps printing in full.
@[app_delab _root_.frequency]
def delabBasaltFrequency : Delab := do
  delabDroppingSideCondition ``_root_.frequency 5 3 someWeightPos

/-- Is `p` an auxiliary `._proof_i` applied to a local hypothesis?

That is the shape a primitive's side condition takes in a *synthesized* generator: the synthesis
rule discharges it with a tactic, the definition elaborator abstracts the result into a
`._proof_i`, and the floated `assume`'s guard reaches it as an argument. Printed in full it is an
unpasteable reference to a synthesis-internal constant; recovered by `gen_side_condition` from the
guard the enclosing `dite` binds, it need not be printed at all.

The `isFVar` conjunct is what makes this a statement about recoverability and not about names: the
local it is applied to is the guard, and the guard is what the autoParam finds in the pasted term's
context. A `._proof_i` closed over nothing local proves something about closed data, which
`gen_side_condition` would have to establish from scratch. -/
def isAuxProofOverLocals (p : Expr) : Bool :=
  p.getAppFn.constName?.any (·.getString!.startsWith "_proof_") && p.getAppArgs.any Expr.isFVar

/-- Render `c`'s arguments at `shown`, dropping its trailing side-condition *proof*, when
`recoverable` says `c`'s `gen_side_condition` autoParam can put it back.

The primitive counterpart of `delabDroppingSideCondition`, separate from it because the two differ
in what they inspect. A combinator's side condition is recoverable from *one* argument (the branch
list), which is also the only thing printed. A primitive's is recoverable from either its data
arguments or the shape of the proof itself, so `recoverable` receives the whole application; and the
arguments worth printing are an explicit subset, since the type parameter is implicit. -/
def delabDroppingProof (c : Name) (arity : Nat) (shown : List Nat) (recoverable : Expr → Bool) :
    Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity c arity
  guard <| recoverable e
  let args ← shown.toArray.mapM fun i => withNaryArg i delab
  let fn := mkIdent (← unresolveNameGlobal c)
  `($fn $args*)

end Delab

/-- The empty generator: produces nothing. -/
def empty : PGen α := ⟨fun {_G} _ _ => Fail.fail⟩

/-- A guarded generator: `f` when `b` holds, otherwise failure.

This is needed for synthesis (see synthesis rules like `s_between_partial` to see why), but ideally
it should be optimized away before the generator is used. -/
def assume (b : Bool) (f : b → PGen α) : PGen α :=
  if h : b then f h else empty

noncomputable instance : Fail SPMF := ⟨Lean.Order.bot⟩

/-! ## Support

`support g` is the set of values `g` can produce. -/

/-- The set of values a generator can produce, via its `SPMF` interpretation. -/
def support (g : PGen α) : α → Prop := SPMF.support g.run

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
  simp only [support, Pure.pure, PGen.pure, eq_iff_iff]
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
theorem support_frequency {gs : List (Nat × PGen α)} (h) :
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
theorem support_oneOf {gs : List (PGen α)} (h) :
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
    support (empty : PGen α) = fun _ => False := by
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

end PGen

end Palamedes

notation v " ∈ " "〚" g "〛" => Palamedes.PGen.support g v
