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
-/

namespace Palamedes

/-! ## Failure-free combinators

The `TGen` mirror of the core generator algebra. Each is the obvious failure-free term, and each
coerces (`TGen.toGen`) to the corresponding `Gen` combinator definitionally — that is what makes the
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

/-- `Gen`'s `Functor.map` is the `Monad` default (`bind` then `pure`), so the witness must mirror that
shape rather than `G`'s native `<$>` to coerce definitionally. -/
protected def map (f : α → β) (x : TGen α) : TGen β :=
  ⟨fun {_G} _ => x.run >>= fun a => Pure.pure (f a)⟩

/-! ### Mirror equations

Each `TGen` combinator coerces to its `Gen` twin. These used to be inlined as `by ext; rfl` inside
every totality lemma; with `total` carrying data the witness and the equation are built separately,
so the equations are stated once here and the lemmas below cite them. -/

@[simp] theorem toGen_pure (a : α) : (TGen.pure a).toGen = Pure.pure a := by ext; rfl

@[simp] theorem toGen_bind (x : TGen α) (f : α → TGen β) :
    (TGen.bind x f).toGen = x.toGen >>= fun a => (f a).toGen := by ext; rfl

@[simp] theorem toGen_pick (x y : TGen α) :
    (TGen.pick x y).toGen = Gen.pick x.toGen y.toGen := by ext; rfl

@[simp] theorem toGen_map (f : α → β) (x : TGen α) :
    (TGen.map f x).toGen = f <$> x.toGen := by ext; rfl

@[simp] theorem toGen_frequency (gs : List (Nat × TGen α)) (h) :
    (TGen.frequency gs h).toGen
      = Gen.frequency (gs.map fun p => (p.1, p.2.toGen))
          (by simpa [List.map_map, Function.comp_def] using h) := by
  ext
  simp only [TGen.toGen, TGen.frequency, Gen.frequency, List.map_map, Function.comp_def]

end TGen

namespace Gen

/-- A generator is `total` when it factors through the failure-free interface `TGen`: a failure-free
witness together with a proof that its coercion is `g`. Equivalently, `g` is definable without
`Fail`, i.e. it never uses `assume`/`empty`.

This is *data*, not a proposition — see the module docstring. `.val` is the witness the synthesizer
emits from; `.property` is what carries a support fact across to it. -/
def total (g : Gen α) : Type 1 := {t : TGen α // t.toGen = g}

def totalList (gs : List (Gen α)) : Type 1 := {ts : List (TGen α) // ts.map TGen.toGen = gs}

def totalWeighted (gs : List (Nat × Gen α)) : Type 1 :=
  {ts : List (Nat × TGen α) // ts.map (fun p => (p.1, p.2.toGen)) = gs}

/-- `frequency` is determined by its branch list: its side condition is a `Prop`, so two calls with
the same list are equal whatever proofs they carry. Needed because `rw`ing the branch list directly
cannot build a motive — the side-condition argument's *type* mentions the list. -/
theorem frequency_congr {gs gs' : List (Nat × Gen α)} (hg : gs = gs') {h h'} :
    frequency gs h = frequency gs' h' := by
  subst hg; rfl

namespace Total

/-! These are `def`s rather than `theorem`s, and carry no `@[simp]`: `total` is `Type`-valued, so
they build witnesses rather than prove propositions. The `totality` tactic drives them with `apply`,
which is unaffected. They must stay **computable** — the witness they assemble is what stage 2 emits
as the generator's definition, so a `Classical.choice` anywhere here would make the emitted
generator noncomputable. That is the direct reason `total_bind` no longer uses `choose`.

**Every one of these is written as a direct `⟨witness, proof⟩`, with tactics confined to the proof
component, and that is load-bearing rather than stylistic.** Written instead as `by obtain ⟨t, rfl⟩ …`
the `subst` puts an `Eq.rec` in the *data* path, which blocks `.val` from projecting — so the emitted
generator cannot be reduced back to generator code and lands in the environment as a witness tree
(`total_bind (total_oneOf …) …`) instead of as a readable generator. `PalamedesTest/Extract.lean`
audits for exactly that. Keep the data direct. -/

def total_pure (a : α) : total (pure a) :=
  ⟨TGen.pure a, by ext; rfl⟩

def total_bind
    (hx : total x)
    (hf : ∀ a, total (f a)) :
    total (x >>= f) :=
  ⟨TGen.bind hx.val (fun a => (hf a).val), by
    rw [TGen.toGen_bind, hx.property]
    exact congrArg _ (funext fun a => (hf a).property)⟩

def total_pick
    (hx : total x)
    (hy : total y) :
    total (pick x y) :=
  ⟨TGen.pick hx.val hy.val, by rw [TGen.toGen_pick, hx.property, hy.property]⟩

def totalList_nil : totalList ([] : List (Gen α)) := ⟨[], rfl⟩

def totalList_cons {x : Gen α} {gs : List (Gen α)}
    (hx : total x)
    (hgs : totalList gs) :
    totalList (x :: gs) :=
  ⟨hx.val :: hgs.val, by rw [List.map_cons, hx.property, hgs.property]⟩

def totalWeighted_nil : totalWeighted ([] : List (Nat × Gen α)) := ⟨[], rfl⟩

def totalWeighted_cons {w : Nat} {g : Gen α} {gs : List (Nat × Gen α)}
    (hg : total g)
    (hgs : totalWeighted gs) :
    totalWeighted ((w, g) :: gs) :=
  ⟨(w, hg.val) :: hgs.val, by
    simp only [List.map_cons]
    rw [hg.property, hgs.property]⟩

/-- The weights of the witness list match those of `gs`, since `toGen` only touches the generator
component. This is the side condition `TGen.frequency` needs, and it has to be available *before* the
proof component so that the witness itself can be built. -/
theorem totalWeighted_fst {gs : List (Nat × Gen α)} (hgs : totalWeighted gs) :
    hgs.val.map Prod.fst = gs.map Prod.fst := by
  -- `conv_rhs`, not a bare `rw`: `hgs`'s own type mentions `gs`, so rewriting it everywhere makes
  -- the motive ill-typed.
  conv_rhs => rw [← hgs.property]
  simp [List.map_map, Function.comp_def]

def total_frequency {gs : List (Nat × Gen α)} {h}
    (hgs : totalWeighted gs) :
    total (frequency gs h) :=
  ⟨TGen.frequency hgs.val (by rw [totalWeighted_fst hgs]; exact h), by
    rw [TGen.toGen_frequency]
    exact frequency_congr hgs.property⟩

def total_oneOf {gs : List (Gen α)} {h}
    (hgs : totalList gs) :
    total (oneOf gs h) :=
  total_frequency (gs := gs.map fun g => (1, g))
    ⟨hgs.val.map fun t => (1, t), by
      conv_rhs => rw [← hgs.property]
      simp [List.map_map, Function.comp_def]⟩

def total_map
    (hx : total x) :
    total (f <$> x) :=
  ⟨TGen.map f hx.val, by rw [TGen.toGen_map, hx.property]⟩

def total_dite
    {g₁ : b = true → Gen α}
    {g₂ : ¬ (b = true) → Gen α}
    (h₁ : (h : b = true) → total (g₁ h))
    (h₂ : (h : ¬(b = true)) → total (g₂ h))
    : total (if h : b then g₁ h else g₂ h) :=
  -- The witness mirrors the `dite` rather than casing on `b` outside it: a `by_cases` here would put
  -- the case split in the data path, where it cannot reduce until `b` is concrete.
  ⟨if hb : b then (h₁ hb).val else (h₂ hb).val, by
    by_cases hb : b = true
    · rw [dif_pos hb, dif_pos hb]; exact (h₁ hb).property
    · rw [dif_neg hb, dif_neg hb]; exact (h₂ hb).property⟩

/- Recursion has no generic totality lemma: each datatype's `unfold` gets its own `X.total_unfold`
in `Palamedes/Data/`, whose witness is that datatype's `unfold` re-run at the failure-free interface
(`TGen`). Because the unfold body never mentions `Fail`, the witness equality is a fixpoint
congruence — see `List.total_unfold`. -/

/-! ### Turning a witness back into generator code

`generator_search` emits `witness.val.run`. Unreduced that is a *proof term*; these lemmas project
`.val` through each constructor above and unfold `TGen.run` to the Basalt combinator underneath, so
the emitted definition reads as a generator. All hold by `rfl` — that is exactly what writing the
witnesses as direct `⟨_, _⟩` buys. -/

@[twitness] theorem val_pure (a : α) : (total_pure a).val = TGen.pure a := rfl

@[twitness] theorem val_bind {x : Gen α} {f : α → Gen β}
    (hx : total x) (hf : ∀ a, total (f a)) :
    (total_bind hx hf).val = TGen.bind hx.val (fun a => (hf a).val) := rfl

@[twitness] theorem val_pick {x y : Gen α} (hx : total x) (hy : total y) :
    (total_pick hx hy).val = TGen.pick hx.val hy.val := rfl

@[twitness] theorem val_map {x : Gen α} {f : α → β} (hx : total x) :
    (total_map (f := f) hx).val = TGen.map f hx.val := rfl

@[twitness] theorem val_listNil : (totalList_nil (α := α)).val = [] := rfl

@[twitness] theorem val_listCons {x : Gen α} {gs : List (Gen α)}
    (hx : total x) (hgs : totalList gs) :
    (totalList_cons hx hgs).val = hx.val :: hgs.val := rfl

@[twitness] theorem val_weightedNil : (totalWeighted_nil (α := α)).val = [] := rfl

@[twitness] theorem val_weightedCons {w : Nat} {g : Gen α} {gs : List (Nat × Gen α)}
    (hg : total g) (hgs : totalWeighted gs) :
    (totalWeighted_cons (w := w) hg hgs).val = (w, hg.val) :: hgs.val := rfl

-- `TGen.frequency`'s body maps over its branch list, so the list has to compute before the
-- per-branch `.run` can project.
attribute [twitness] List.map_cons List.map_nil

/-- `Eq.rec` transports a `total g₁` to a `total g₂`, but the witness itself is a `TGen α` either
way, so `.val` is invariant under the transport. The `totality` tactic's `split` step introduces
these casts around each match arm; without this the projection stops there. -/
@[twitness] theorem val_eqRec {g₁ g₂ : Gen α} (h : g₁ = g₂) (t : total g₁) :
    (h ▸ t).val = t.val := by cases h; rfl

end Total

end Gen

end Palamedes
