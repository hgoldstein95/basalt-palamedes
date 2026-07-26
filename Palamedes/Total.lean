/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.CorrectGen
import Palamedes.Extract
import Palamedes.RuleSets

/-!
# Totality (assume-freedom)

A generator is `total` when it never fails — equivalently, when it is definable *without* the `Fail`
capability. We make that precise as **factoring through `TGen`**: `total g` is the type of
failure-free `t : TGen α` with `t.toGen = g`.

`total` is **`Type`-valued, not `Prop`-valued**, and that is load-bearing rather than incidental. The
witness `t` is the failure-free generator itself, and `t.run` is already a Basalt-shaped generator
(`∀ {G} [Gen G], G α`) — so a totality proof *is* the term we want to emit. Stated as an `∃` the
witness was sealed behind `Exists`, and the compositional lemmas had to recover it with `choose`,
pulling `Classical.choice` into every totality fact and making the result noncomputable. As a
subtype the witness projects out with `.val`, the lemmas are computable, and `t.toGen = g` is what
transfers a support fact from `g` to the emitted generator.

This is a structural, syntactic notion of totality — "no `assume`" — for the polymorphic carrier. It is
deliberately *not* Basalt's almost-sure termination (`SPMF.IsPMF`, i.e. mass = 1): the two agree on
every non-recursive generator, but disagree on recursion (an assume-free `unfold` can still diverge
with probability 1, e.g. an always-`cons` body). Almost-sure termination is a strictly stronger
property — a separate predicate (`IsPMF ∘ run`), orthogonal to this one.

Because `TGen` cannot mention `Fail`, every combinator that does not fail has a `TGen` witness, and
the introduction lemmas below build those witnesses compositionally. The recursive case
(`X.total_unfold`) lives with each datatype in `Palamedes/Data/`, because the witness is that
datatype's own `unfold` re-instantiated at the failure-free interface.

The combinator basis below is the one place where the two interfaces are both written out, and it
has to be: a combinator's arguments are *generators*, so its `TGen` and `PGen` spellings genuinely
differ in argument type and neither can be the image of the other. A datatype's **primitives** go
the other way — defined once at `TGen`, with the `PGen` form as `TGen.toGen` of it (`TGen.arbNat`,
`TGen.choose`, `TGen.elements`, …). Their `total_*` lemmas are then `⟨TGen.foo, rfl⟩`, with no
second body to keep in agreement and no reconnecting lemma to forget.

The dividing line is whether the witness has a compositional route, not whether the generator can
fail. A *composite* over the primitives stays an ordinary `PGen` definition — `PGen.gt` is
`(lo + 1 + ·) <$> arbNat`, and `total_gt` is `total_map total_arbNat` — because the registry already
assembles its witness, so there is no second body to write in either direction.
-/

namespace Palamedes

/-! ## Failure-free combinators

The `TGen` mirror of the core generator algebra. Each is the obvious failure-free term, and each
coerces (`TGen.toGen`) to the corresponding `PGen` combinator definitionally — that is what makes the
totality witnesses below close by `rfl`. -/

namespace TGen

protected def pure (a : α) : TGen α := ⟨fun {_G} _ => Pure.pure a⟩

protected def bind (x : TGen α) (f : α → TGen β) : TGen β :=
  ⟨fun {_G} _ => x.run >>= fun a => (f a).run⟩

def pick (x y : TGen α) : TGen α :=
  ⟨fun {_G} _ => RandomChoice.pick (fun () => x.run) (fun () => y.run)⟩

def frequency (gs : List (Nat × TGen α)) (h : 0 < (gs.map Prod.fst).sum := by simp) : TGen α :=
  ⟨fun {_G} _ =>
    _root_.frequency (gs.map fun p => (p.1, fun _ => p.2.run))
      (by simpa [List.map_map, Function.comp_def] using h)⟩

/-- `PGen`'s `Functor.map` is the `Monad` default (`bind` then `pure`), so the witness must mirror that
shape rather than `G`'s native `<$>` to coerce definitionally. -/
protected def map (f : α → β) (x : TGen α) : TGen β :=
  ⟨fun {_G} _ => x.run >>= fun a => Pure.pure (f a)⟩

/-! ### Mirror equations

Each `TGen` combinator coerces to its `PGen` twin. These used to be inlined as `by ext; rfl` inside
every totality lemma; with `total` carrying data the witness and the equation are built separately,
so the equations are stated once here and the lemmas below cite them. -/

@[simp] theorem toGen_pure (a : α) : (TGen.pure a).toGen = Pure.pure a := by ext; rfl

@[simp] theorem toGen_bind (x : TGen α) (f : α → TGen β) :
    (TGen.bind x f).toGen = x.toGen >>= fun a => (f a).toGen := by ext; rfl

@[simp] theorem toGen_pick (x y : TGen α) :
    (TGen.pick x y).toGen = PGen.pick x.toGen y.toGen := by ext; rfl

@[simp] theorem toGen_map (f : α → β) (x : TGen α) :
    (TGen.map f x).toGen = f <$> x.toGen := by ext; rfl

@[simp] theorem toGen_frequency (gs : List (Nat × TGen α)) (h) :
    (TGen.frequency gs h).toGen
      = PGen.frequency (gs.map fun p => (p.1, p.2.toGen))
          (by simpa [List.map_map, Function.comp_def] using h) := by
  ext
  simp only [TGen.toGen, TGen.frequency, PGen.frequency, List.map_map, Function.comp_def]

end TGen

/-- The `TGen` combinator basis: the failure-free mirror of the core generator algebra, as data.

Two stages need the list rather than the definitions. `extractWitness` delta-unfolds exactly these
to turn a totality witness back into generator code, and `PalamedesTest/Extract.lean` reads a
survivor of that unfolding as evidence that extraction stopped early. Both must agree on what counts
as basis, so neither enumerates it.

A datatype's own primitive spelled at `TGen` — `TGen.arbNat`, `TGen.elements` — is deliberately not
here. It is the generator the Basalt shape is projected from, not machinery to be unfolded away. -/
def tgenBasis : Array Lean.Name :=
  #[``TGen.pure, ``TGen.bind, ``TGen.pick, ``TGen.frequency, ``TGen.map, ``TGen.toGen]

namespace PGen

/-- A generator is `total` when it factors through the failure-free interface `TGen`: a failure-free
witness together with a proof that its coercion is `g`. Equivalently, `g` is definable without
`Fail`, i.e. it never uses `assume`/`empty`.

This is *data*, not a proposition — see the module docstring. `.val` is the witness the synthesizer
emits from; `.property` is what carries a support fact across to it. -/
def total (g : PGen α) : Type 1 := {t : TGen α // t.toGen = g}

def totalList (gs : List (PGen α)) : Type 1 := {ts : List (TGen α) // ts.map TGen.toGen = gs}

def totalWeighted (gs : List (Nat × PGen α)) : Type 1 :=
  {ts : List (Nat × TGen α) // ts.map (fun p => (p.1, p.2.toGen)) = gs}

/-- `frequency` is determined by its branch list: its side condition is a `Prop`, so two calls with
the same list are equal whatever proofs they carry. Needed because `rw`ing the branch list directly
cannot build a motive — the side-condition argument's *type* mentions the list. -/
theorem frequency_congr {gs gs' : List (Nat × PGen α)} (hg : gs = gs') {h h'} :
    frequency gs h = frequency gs' h' := by
  subst hg; rfl

namespace Total

/-! These are `def`s rather than `theorem`s, and carry no `@[simp]`: `total` is `Type`-valued, so
they build witnesses rather than prove propositions.

Each is `@[total]`, exactly like a per-datatype leaf: the generic combinator basis has no privileged
status in the descent, and `Synthesizer/Totality.lean` names none of them. The tag both registers
the rule and fixes the head it reconstructs, so `total_oneOf` and `total_frequency` can no longer
race however they are ordered here.

They must stay **computable** — the witness they assemble is what stage 2 emits
as the generator's definition, so a `Classical.choice` anywhere here would make the emitted
generator noncomputable. That is the direct reason `total_bind` no longer uses `choose`.

**Every one of these is written as a direct `⟨witness, proof⟩`, with tactics confined to the proof
component, and that is load-bearing rather than stylistic.** Written instead as `by obtain ⟨t, rfl⟩ …`
the `subst` puts an `Eq.rec` in the *data* path, which blocks `.val` from projecting — so the emitted
generator cannot be reduced back to generator code and lands in the environment as a witness tree
(`total_bind (total_oneOf …) …`) instead of as a readable generator. `PalamedesTest/Extract.lean`
audits for exactly that. Keep the data direct. -/

@[total]
def total_pure (a : α) : total (pure a) :=
  ⟨TGen.pure a, by ext; rfl⟩

@[total]
def total_bind
    (hx : total x)
    (hf : ∀ a, total (f a)) :
    total (x >>= f) :=
  ⟨TGen.bind hx.val (fun a => (hf a).val), by
    rw [TGen.toGen_bind, hx.property]
    exact congrArg _ (funext fun a => (hf a).property)⟩

@[total]
def total_pick
    (hx : total x)
    (hy : total y) :
    total (pick x y) :=
  ⟨TGen.pick hx.val hy.val, by rw [TGen.toGen_pick, hx.property, hy.property]⟩

@[total]
def totalList_nil : totalList ([] : List (PGen α)) := ⟨[], rfl⟩

@[total]
def totalList_cons {x : PGen α} {gs : List (PGen α)}
    (hx : total x)
    (hgs : totalList gs) :
    totalList (x :: gs) :=
  ⟨hx.val :: hgs.val, by rw [List.map_cons, hx.property, hgs.property]⟩

@[total]
def totalWeighted_nil : totalWeighted ([] : List (Nat × PGen α)) := ⟨[], rfl⟩

@[total]
def totalWeighted_cons {w : Nat} {g : PGen α} {gs : List (Nat × PGen α)}
    (hg : total g)
    (hgs : totalWeighted gs) :
    totalWeighted ((w, g) :: gs) :=
  ⟨(w, hg.val) :: hgs.val, by
    simp only [List.map_cons]
    rw [hg.property, hgs.property]⟩

/-- The weights of the witness list match those of `gs`, since `toGen` only touches the generator
component. This is the side condition `TGen.frequency` needs, and it has to be available *before* the
proof component so that the witness itself can be built. -/
theorem totalWeighted_fst {gs : List (Nat × PGen α)} (hgs : totalWeighted gs) :
    hgs.val.map Prod.fst = gs.map Prod.fst := by
  -- `conv_rhs`, not a bare `rw`: `hgs`'s own type mentions `gs`, so rewriting it everywhere makes
  -- the motive ill-typed.
  conv_rhs => rw [← hgs.property]
  simp [List.map_map, Function.comp_def]

@[total]
def total_frequency {gs : List (Nat × PGen α)} {h}
    (hgs : totalWeighted gs) :
    total (frequency gs h) :=
  ⟨TGen.frequency hgs.val (by rw [totalWeighted_fst hgs]; exact h), by
    rw [TGen.toGen_frequency]
    exact frequency_congr hgs.property⟩

@[total]
def total_oneOf {gs : List (PGen α)} {h}
    (hgs : totalList gs) :
    total (oneOf gs h) :=
  total_frequency (gs := gs.map fun g => (1, g))
    ⟨hgs.val.map fun t => (1, t), by
      conv_rhs => rw [← hgs.property]
      simp [List.map_map, Function.comp_def]⟩

@[total]
def total_map
    (hx : total x) :
    total (f <$> x) :=
  ⟨TGen.map f hx.val, by rw [TGen.toGen_map, hx.property]⟩

/-- The conditional lives **inside** `TGen.mk`, not outside it, and that placement is the whole
content of this lemma — the same trick, and for the same reason, as `X.total_cases`.

Written the other way round (`if hb : b then (h₁ hb).val else (h₂ hb).val`) the witness is a `dite`
whose branches are `TGen`s, so the `.run` the Basalt shape projects with has a `dite` between it and
the `TGen.mk`s and simply does not cancel. What gets emitted is
`(if hb : … then { run := … } else { run := … }).run` — structure literals, eta-expanded branches
and a `._proof_1` reference, in a term that is supposed to be readable and re-elaborable. With the
`mk` outermost the projection cancels at the top and the `dite` is left where it belongs, in the
generator's body.

This was invisible while the corpus was declared at the `Palamedes.PGen` carrier, which emits the
optimized generator and never projects the witness. `genBST` is the canary. -/
@[total]
def total_dite
    {g₁ : b = true → PGen α}
    {g₂ : ¬ (b = true) → PGen α}
    (h₁ : (h : b = true) → total (g₁ h))
    (h₂ : (h : ¬(b = true)) → total (g₂ h))
    : total (if h : b then g₁ h else g₂ h) :=
  -- Still not a `by_cases` on `b`: that would put the case split in the data path, where it cannot
  -- reduce until `b` is concrete. The `dite` stays, it just moves inside the `mk`.
  ⟨⟨fun {_G} _ => if hb : b then (h₁ hb).val.run else (h₂ hb).val.run⟩, by
    by_cases hb : b = true
    · simp only [dif_pos hb]; exact (h₁ hb).property
    · simp only [dif_neg hb]; exact (h₂ hb).property⟩

/-- The non-dependent `ite`, which is **not** an instance of `total_dite`: that one is keyed on
`dite` and on a `Bool` condition read as `b = true`, and dispatch is by head constant, so an
`ite` over an arbitrary decidable `Prop` matched no rule at all.

What that cost was invisible for as long as the corpus was declared at the carrier. `totality` is
`repeat' first | … | split`, so a node with no rule does not fail — it falls through to `split`,
which leaves a `Decidable.rec` and an `Eq.mpr` per arm in the witness's **data** path. Reading a
generator out of that is what `G α` does, and the code generator rejects it outright:
"code generator does not support recursor `Decidable.rec`". A predicate as ordinary as
`isComplete`'s `n == 0` reaches it.

`mk` outermost, for the reason `total_dite` gives. -/
@[total]
def total_ite {c : Prop} [Decidable c] {g₁ g₂ : PGen α}
    (h₁ : total g₁)
    (h₂ : total g₂)
    : total (if c then g₁ else g₂) :=
  ⟨⟨fun {_G} _ => if c then h₁.val.run else h₂.val.run⟩, by
    by_cases hc : c
    · simp only [if_pos hc]; exact h₁.property
    · simp only [if_neg hc]; exact h₂.property⟩

/- Recursion has no generic totality lemma: each datatype's `unfold` gets its own `X.total_unfold`
in `Palamedes/Data/`, whose witness is that datatype's `unfold` re-run at the failure-free interface
(`TGen`). Because the unfold body never mentions `Fail`, the witness equality is a fixpoint
congruence — see `List.total_unfold`. -/

/-! ### Turning a witness back into generator code

`generator_search` emits `witness.val.run`. Unreduced that is a *proof term*; these lemmas project
`.val` through each constructor above and unfold `TGen.run` to the Basalt combinator underneath, so
the emitted definition reads as a generator. All hold by `rfl` — that is exactly what writing the
witnesses as direct `⟨_, _⟩` buys. -/

@[totality_witness] theorem val_pure (a : α) : (total_pure a).val = TGen.pure a := rfl

@[totality_witness] theorem val_bind {x : PGen α} {f : α → PGen β}
    (hx : total x) (hf : ∀ a, total (f a)) :
    (total_bind hx hf).val = TGen.bind hx.val (fun a => (hf a).val) := rfl

@[totality_witness] theorem val_pick {x y : PGen α} (hx : total x) (hy : total y) :
    (total_pick hx hy).val = TGen.pick hx.val hy.val := rfl

@[totality_witness] theorem val_map {x : PGen α} {f : α → β} (hx : total x) :
    (total_map (f := f) hx).val = TGen.map f hx.val := rfl

@[totality_witness] theorem val_listNil : (totalList_nil (α := α)).val = [] := rfl

@[totality_witness] theorem val_listCons {x : PGen α} {gs : List (PGen α)}
    (hx : total x) (hgs : totalList gs) :
    (totalList_cons hx hgs).val = hx.val :: hgs.val := rfl

@[totality_witness] theorem val_weightedNil : (totalWeighted_nil (α := α)).val = [] := rfl

@[totality_witness] theorem val_weightedCons {w : Nat} {g : PGen α} {gs : List (Nat × PGen α)}
    (hg : total g) (hgs : totalWeighted gs) :
    (totalWeighted_cons (w := w) hg hgs).val = (w, hg.val) :: hgs.val := rfl

-- `TGen.frequency`'s body maps over its branch list, so the list has to compute before the
-- per-branch `.run` can project.
attribute [totality_witness] List.map_cons List.map_nil

/-- `Eq.rec` transports a `total g₁` to a `total g₂`, but the witness itself is a `TGen α` either
way, so `.val` is invariant under the transport. The `totality` tactic's `split` step introduces
these casts around each match arm; without this the projection stops there. -/
@[totality_witness] theorem val_eqRec {g₁ g₂ : PGen α} (h : g₁ = g₂) (t : total g₁) :
    (h ▸ t).val = t.val := by cases h; rfl

end Total

end PGen

end Palamedes
