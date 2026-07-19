import Palamedes.CorrectGen
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

namespace Total

/-! These are `def`s rather than `theorem`s, and carry no `@[simp]`: `total` is `Type`-valued, so
they build witnesses rather than prove propositions. The `totality` tactic drives them with `apply`,
which is unaffected. They must stay **computable** — the witness they assemble is what stage 2 emits
as the generator's definition, so a `Classical.choice` anywhere here would make the emitted
generator noncomputable. That is the direct reason `total_bind` no longer uses `choose`. -/

def total_pure (a : α) : total (pure a) :=
  ⟨TGen.pure a, by ext; rfl⟩

def total_bind
    (hx : total x)
    (hf : ∀ a, total (f a)) :
    total (x >>= f) := by
  obtain ⟨tx, rfl⟩ := hx
  refine ⟨TGen.bind tx (fun a => (hf a).val), ?_⟩
  rw [TGen.toGen_bind]
  exact congrArg _ (funext fun a => (hf a).property)

def total_pick
    (hx : total x)
    (hy : total y) :
    total (pick x y) := by
  obtain ⟨tx, rfl⟩ := hx
  obtain ⟨ty, rfl⟩ := hy
  exact ⟨TGen.pick tx ty, by ext; rfl⟩

def totalList_nil : totalList ([] : List (Gen α)) := ⟨[], rfl⟩

def totalList_cons {x : Gen α} {gs : List (Gen α)}
    (hx : total x)
    (hgs : totalList gs) :
    totalList (x :: gs) := by
  obtain ⟨tx, rfl⟩ := hx
  obtain ⟨ts, rfl⟩ := hgs
  exact ⟨tx :: ts, rfl⟩

def totalWeighted_nil : totalWeighted ([] : List (Nat × Gen α)) := ⟨[], rfl⟩

def totalWeighted_cons {w : Nat} {g : Gen α} {gs : List (Nat × Gen α)}
    (hg : total g)
    (hgs : totalWeighted gs) :
    totalWeighted ((w, g) :: gs) := by
  obtain ⟨tg, rfl⟩ := hg
  obtain ⟨ts, rfl⟩ := hgs
  exact ⟨(w, tg) :: ts, rfl⟩

def total_frequency {gs : List (Nat × Gen α)} {h}
    (hgs : totalWeighted gs) :
    total (frequency gs h) := by
  obtain ⟨ts, rfl⟩ := hgs
  refine ⟨TGen.frequency ts (by simpa [List.map_map, Function.comp_def] using h), ?_⟩
  ext
  simp only [TGen.toGen, TGen.frequency, frequency, List.map_map, Function.comp_def]

def total_oneOf {gs : List (Gen α)} {h}
    (hgs : totalList gs) :
    total (oneOf gs h) := by
  obtain ⟨ts, rfl⟩ := hgs
  exact total_frequency ⟨ts.map fun t => (1, t), by simp [List.map_map, Function.comp_def]⟩

def total_map
    (hx : total x) :
    total (f <$> x) := by
  obtain ⟨tx, rfl⟩ := hx
  exact ⟨TGen.map f tx, by ext; rfl⟩

def total_dite
    {g₁ : b = true → Gen α}
    {g₂ : ¬ (b = true) → Gen α}
    (h₁ : (h : b = true) → total (g₁ h))
    (h₂ : (h : ¬(b = true)) → total (g₂ h))
    : total (if h : b then g₁ h else g₂ h) := by
  -- `cases b` rather than `by_cases`: the latter can go through `Classical.byCases`, which does not
  -- eliminate into `Type`. Casing the `Bool` lets the `Decidable` instance reduce, so each branch
  -- closes by defeq.
  cases b
  · exact h₂ (by simp)
  · exact h₁ rfl

/- Recursion has no generic totality lemma: each datatype's `unfold` gets its own `X.total_unfold`
in `Palamedes/Data/`, whose witness is that datatype's `unfold` re-run at the failure-free interface
(`TGen`). Because the unfold body never mentions `Fail`, the witness equality is a fixpoint
congruence — see `List.total_unfold`. -/

end Total

end Gen

end Palamedes
