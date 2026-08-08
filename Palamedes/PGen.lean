/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/
import Basalt

/-!
# Palamedes Generators

A Palamedes `PGen α` wraps a `Gen`-polymorphic Basalt generator that additionally supports failure
(`Fail G`); the wrapped term `g.run` is the bare Basalt generator, instantiable at `SPMF` for proofs
or `Plausible.Gen` for sampling. Synthesis builds `PGen` terms as data, and a generator acquires
meaning only by interpreting its `run` at a chosen `G` — the proof interpretation being Basalt's
sub-probability mass function, so `support` is `SPMF.support`.
-/

namespace Palamedes

open Lean.Order

/-- The failure capability: a generator monad with a designated "produces nothing" element.

We need this because Basalt's CCPO bottom (`Lean.Order.bot`) is `noncomputable`, and it conflates
rejection with divergence.  -/
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

/-! ## Basalt's uniform range draw

`chooseNat` is Basalt vocabulary, like `pick` and `frequency` below, rather than a generator
Palamedes defines: `TGen Nat` is exactly the type of a `Gen`-polymorphic `G Nat`, so the failure-free
view of it costs a `TGen.mk` and nothing else, and the `PGen` view is that coerced.

The explicit `namespace TGen` block, outside the `PGen` one, is the placement every `Data/` module
uses for its own primitives; `Data/Nat.lean` documents what goes wrong without it. -/

namespace TGen

/-- A uniform draw from `[lo, hi]`, inclusive. -/
def choose (lo hi : Nat) (h : lo ≤ hi := by gen_side_condition) : TGen Nat :=
  ⟨fun {_G} _ => chooseNat lo hi h⟩

end TGen

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

/-- A uniform draw from `[lo, hi]`, inclusive. Failure-free, so it is `TGen.choose` coerced rather
than a second body: `total_choose` is then `⟨TGen.choose lo hi h, rfl⟩`, with no lemma reconnecting
two spellings. -/
def choose (lo hi : Nat) (h : lo ≤ hi := by gen_side_condition) : PGen Nat :=
  (TGen.choose lo hi h).toGen

section Delab

open Lean PrettyPrinter Delaborator SubExpr

/-- The first `autoParam` binder of `ty`: its argument index, and the tactic declaring it.

Each combinator here declares exactly one, as its trailing argument, so the first is the only one;
finding it is what saves every registration below from restating the position. -/
private partial def autoParamAt? (ty : Expr) (i : Nat := 0) : Option (Nat × Name) :=
  match ty with
  | .forallE _ d b _ =>
    match d.getAutoParamTactic? with
    | some (.const n _) => some (i, n)
    | _ => autoParamAt? b (i + 1)
  | _ => none

/-- The heartbeat ceiling for a side-condition tactic run while printing.

Explicit rather than the ambient budget: inheriting it would let one stuck `autoParam` burn all of a
corpus file's raised `maxHeartbeats` inside the printer, and would make the same term print
differently depending on how much of the budget elaboration had already spent. -/
private def sideConditionHeartbeats : Nat := 1000

/-- Can `c`'s `autoParam` re-derive the side-condition proof that `e` carries, in `e`'s own context?

The tactic is *run*, against the proof's type, in the local context the printed term would be pasted
into — so the judgement is the pasteability contract itself rather than a proxy for it, in both
directions. A check on the proof's *shape* silently stops saying yes under any of the ways a proof
spine drifts: simp's `dite_congr` transports a bound guard into each arm whether or not it rewrote
the guard, `Meta.reduce` skips proofs, and `whnf` will not unfold the resulting `Eq.mpr_prop`.
`PalamedesTest/GeneratorAPI.lean` pins both answers — `renderUnrecoverable` is the one the tactic
cannot discharge — since a check that only ever says yes is indistinguishable from no check. -/
def autoParamRecovers (c : Name) (e : Expr) : MetaM Bool :=
  open Lean.Meta in do
  let some ci := (← getEnv).find? c | return false
  let some (i, tacDecl) := autoParamAt? ci.type | return false
  let some arg := e.getAppArgs[i]? | return false
  let .ok stx := Elab.evalSyntaxConstant (← getEnv) (← getOptions) tacDecl | return false
  try
    -- Restores the `Core` state as well as the `Meta` one, so a failing `simp_all` does not leave
    -- its own error behind as a message on the declaration being printed.
    withoutModifyingState do
      withTheReader Core.Context ({ · with maxHeartbeats := sideConditionHeartbeats * 1000 }) do
        Core.withCurrHeartbeats do
          let mv ← mkFreshExprMVar (← inferType arg)
          let (gs, _) ← Elab.runTactic mv.mvarId! stx
          return gs.isEmpty
  catch ex =>
    if ex.isInterrupt then throw ex
    return false

/-- Render `c`'s arguments at `shown`, dropping its trailing side-condition proof, when `c`'s
`autoParam` can put that proof back.

Every constant an emitted term can name while carrying a side-condition `autoParam` needs a
registration: the choice combinators at each spelling a reader meets — Basalt's `frequency`, which
both emitted shapes choose with, plus `PGen.oneOf`/`PGen.frequency`, which `palamedes.debug`, the
`optimize_gen` tactic and `PalamedesTest/Optimizer/Rewrites.lean` print — and the primitives, Basalt's
`chooseNat` and Palamedes' own `elements` (`Data/STLC/Context.lean`) at both its spellings. Miss one
and a `._proof_i` reference reappears in a pinned term. The proof itself is erased either way; this
is a printing concern, solved in the printer. -/
def delabDroppingProof (c : Name) (arity : Nat) (shown : List Nat) : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity c arity
  guard <| ← autoParamRecovers c e
  let args ← shown.toArray.mapM fun i => withNaryArg i delab
  let fn := mkIdent (← unresolveNameGlobal c)
  `($fn $args*)

@[app_delab Palamedes.PGen.oneOf]
def delabOneOf : Delab :=
  delabDroppingProof ``Palamedes.PGen.oneOf 3 [1]

@[app_delab Palamedes.PGen.frequency]
def delabFrequency : Delab :=
  delabDroppingProof ``Palamedes.PGen.frequency 3 [1]

-- `_root_`-qualified: this section is inside `namespace Palamedes.PGen`, where a bare `frequency`
-- resolves to the carrier's combinator. Unqualified, this silently registers a *second* delaborator
-- for `PGen.frequency` and Basalt's keeps printing in full.
@[app_delab _root_.frequency]
def delabBasaltFrequency : Delab :=
  delabDroppingProof ``_root_.frequency 5 [3]

/-- Print `chooseNat lo hi` without its side-condition proof, so `generator_search?` output
re-elaborates (`chooseNat`'s `gen_side_condition` autoParam recovers it). -/
@[app_delab _root_.chooseNat]
def delabChooseNat : Delab :=
  delabDroppingProof ``_root_.chooseNat 5 [2, 3]

end Delab

/-- The empty generator: produces nothing. -/
def empty : PGen α := ⟨fun {_G} _ _ => Fail.fail⟩

/-- A guarded generator: `f` when `b` holds, otherwise failure.

This is needed for synthesis (see synthesis rules like `s_between_partial` to see why), but ideally
it should be optimized away before the generator is used. -/
def assume (b : Bool) (f : b → PGen α) : PGen α :=
  if h : b then f h else empty

noncomputable instance : Fail SPMF := ⟨Lean.Order.bot⟩

/-! ## Distributing `.run` over a case split

A generator built by `assume` or by a `dite`-guarded synthesis rule has its case split *outside* the
`PGen.mk`, so `.run` sits on top of the `dite` rather than inside each arm and the wrapper never
cancels. These push it inward, for `extractPartialWitness` (`Synthesizer/FrontEnd.lean`), the only
consumer. `TGen` needs no counterpart: `Total.lean`'s discipline puts every case split *inside*
`TGen.mk`, which a `total_*` lemma can do because it chooses how to spell its witness, whereas a
`PGen` is whatever synthesis built.

Deliberately **not** `@[simp]`. Pushing `.run` inward is the normal form one stage wants, not one
the library wants everywhere — every `support` proof in `Data/` reasons about a generator with the
projection where synthesis left it. -/

theorem run_dite {c : Prop} [Decidable c] {a : c → PGen α} {b : ¬c → PGen α}
    {G : Type → Type} [Gen G] [Fail G] :
    (dite c a b).run (G := G) = dite c (fun h => (a h).run) (fun h => (b h).run) := by
  split <;> rfl

theorem run_ite {c : Prop} [Decidable c] {a b : PGen α}
    {G : Type → Type} [Gen G] [Fail G] :
    (ite c a b).run (G := G) = ite c a.run b.run := by
  split <;> rfl

end PGen

/-- The carrier's combinator basis, plus the coercion that ends it. `tgenBasis` (`Total.lean`) is
its counterpart on the totality path, and has the same contract: `extractPartialWitness` unfolds
exactly these, and `PalamedesTest/Extract.lean` reads a survivor as evidence that it stopped early.

`TGen.toGen` is here because a datatype's assume-free primitive is defined at `TGen` and coerced, so
unfolding the coercion turns `PGen.arbNat` into `TGen.arbNat.run` — a generator, and the point at
which unfolding should stop. A datatype's primitive itself is never in a basis; `PGen.choose` is,
because what it names is Basalt's `chooseNat` rather than a generator Palamedes defines. -/
def pgenBasis : Array Lean.Name :=
  #[``PGen.pure, ``PGen.bind, ``PGen.pick, ``PGen.frequency, ``PGen.oneOf, ``PGen.assume,
    ``PGen.empty, ``PGen.choose, ``TGen.toGen]

namespace PGen

/-! ## Support -/

/-- The set of values a generator can produce, via its `SPMF` interpretation. -/
def support (g : PGen α) : α → Prop := SPMF.support g.run

namespace Support

theorem support_ext {g : PGen α} {P : α → Prop} (h : ∀ a, a ∈ SPMF.support g.run ↔ P a) :
    support g = P :=
  funext fun a => propext (h a)

/-- Reindexing along `frequency`'s map. -/
theorem exists_mem_map_weighted {α : Type u} {β : Type v} {gs : List (Nat × α)} (m : α → β) {R : β → Prop} :
    (∃ w b, (w, b) ∈ gs.map (fun p => (p.1, m p.2)) ∧ 0 < w ∧ R b)
      ↔ ∃ w g, (w, g) ∈ gs ∧ 0 < w ∧ R (m g) := by
  constructor
  · rintro ⟨w, b, hmem, hw, hb⟩
    obtain ⟨⟨w', g⟩, hmem', he⟩ := List.mem_map.mp hmem
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨w', g, hmem', hw, hb⟩
  · rintro ⟨w, g, hmem, hw, hg⟩
    exact ⟨w, m g, List.mem_map.mpr ⟨(w, g), hmem, rfl⟩, hw, hg⟩

/-- `exists_mem_map_weighted` at `oneOf`'s all-ones weighting, where the weight condition is
vacuous. -/
theorem exists_mem_map_uniform {α : Type u} {gs : List α} {R : α → Prop} :
    (∃ w g, (w, g) ∈ gs.map (fun g => (1, g)) ∧ 0 < w ∧ R g) ↔ ∃ g ∈ gs, R g := by
  constructor
  · rintro ⟨w, g, hmem, _, hg⟩
    obtain ⟨g', hmem', he⟩ := List.mem_map.mp hmem
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact ⟨g', hmem', hg⟩
  · rintro ⟨g, hmem, hg⟩
    exact ⟨1, g, List.mem_map.mpr ⟨g, hmem, rfl⟩, Nat.one_pos, hg⟩

/-- The `SPMF` interpretation of `empty` is the bottom distribution, whose support is empty. -/
theorem support_bot : SPMF.support (Lean.Order.bot : SPMF α) = (∅ : Set α) := by
  ext a
  rw [show (Lean.Order.bot : SPMF α) = CCPO.csup (chain_empty (SPMF α)) from rfl,
    SPMF.mem_support_csup]
  simp [empty_chain]

@[simp]
theorem support_pure :
    support (pure a) = (· = a) := by
  refine support_ext fun x => ?_
  show x ∈ SPMF.support (Pure.pure a) ↔ x = a
  simp

@[simp]
theorem support_bind :
    support (x >>= f) = fun b => ∃ a, support x a ∧ support (f a) b := by
  refine support_ext fun b => ?_
  show b ∈ SPMF.support (x.run >>= fun a => (f a).run) ↔ _
  simp only [SPMF.support_bind, Set.mem_setOf_eq]
  rfl

@[simp]
theorem support_pick :
    support (pick x y) = fun a => support x a ∨ support y a := by
  refine support_ext fun a => ?_
  show a ∈ SPMF.support (RandomChoice.pick (fun () => x.run) (fun () => y.run)) ↔ _
  simp only [SPMF.support_pick, Set.mem_union]
  rfl

@[simp]
theorem support_frequency {gs : List (Nat × PGen α)} (h) :
    support (frequency gs h) = fun a => ∃ w g, (w, g) ∈ gs ∧ 0 < w ∧ support g a := by
  refine support_ext fun a => ?_
  show a ∈ SPMF.support (_root_.frequency (gs.map fun p => (p.1, fun _ => p.2.run))
      (by simpa [List.map_map, Function.comp_def] using h)) ↔ _
  rw [SPMF.support_frequency]
  simp only [Set.mem_setOf_eq]
  exact exists_mem_map_weighted (m := fun (g : PGen α) (_ : Unit) => (g.run : SPMF α))

@[simp]
theorem support_oneOf {gs : List (PGen α)} (h) :
    support (oneOf gs h) = fun a => ∃ g ∈ gs, support g a := by
  funext a
  simp only [oneOf, support_frequency, eq_iff_iff]
  exact exists_mem_map_uniform

@[simp]
theorem support_choose :
    support (choose lo hi h) = fun a => lo ≤ a ∧ a ≤ hi := by
  refine support_ext fun v => ?_
  show v ∈ SPMF.support (chooseNat lo hi h) ↔ _
  exact SPMF.mem_support_chooseNat_iff

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
  refine support_ext fun b => ?_
  show b ∈ SPMF.support (x.run >>= fun a => Pure.pure (f a)) ↔ _
  simp only [SPMF.support_bind, SPMF.support_pure, Set.mem_setOf_eq, Set.mem_singleton_iff]
  rfl

end Support

end PGen

end Palamedes

notation v " ∈ " "〚" g "〛" => Palamedes.PGen.support g v
