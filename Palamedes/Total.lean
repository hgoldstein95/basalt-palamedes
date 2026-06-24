import Palamedes.CorrectGen
import Palamedes.RuleSets

/-!
# Totality (assume-freedom)

A generator is `total` when it never fails — equivalently, when it is definable *without* the `Fail`
capability. We make that precise as **factoring through `TGen`**: `total g` holds exactly when there
is a failure-free `t : TGen α` with `t.toGen = g`.

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

/-- `Gen`'s `Functor.map` is the `Monad` default (`bind` then `pure`), so the witness must mirror that
shape rather than `G`'s native `<$>` to coerce definitionally. -/
protected def map (f : α → β) (x : TGen α) : TGen β :=
  ⟨fun {_G} _ => x.run >>= fun a => Pure.pure (f a)⟩

end TGen

namespace Gen

/-- A generator is `total` when it factors through the failure-free interface `TGen`: there is a
failure-free witness whose coercion is `g`. Equivalently, `g` is definable without `Fail`, i.e. it
never uses `assume`/`empty`. -/
def total (g : Gen α) : Prop := ∃ t : TGen α, t.toGen = g

namespace Total

@[simp, aesop safe (rule_sets := [totality])]
theorem total_pure (a : α) : total (pure a) :=
  ⟨TGen.pure a, by ext; rfl⟩

@[simp, aesop safe (rule_sets := [totality])]
theorem total_bind
    (hx : total x)
    (hf : ∀ a, total (f a)) :
    total (x >>= f) := by
  obtain ⟨tx, rfl⟩ := hx
  choose tf hf using hf
  have : f = fun a => (tf a).toGen := funext fun a => (hf a).symm
  subst this
  exact ⟨TGen.bind tx tf, by ext; rfl⟩

@[simp, aesop safe (rule_sets := [totality])]
theorem total_pick
    (hx : total x)
    (hy : total y) :
    total (pick x y) := by
  obtain ⟨tx, rfl⟩ := hx
  obtain ⟨ty, rfl⟩ := hy
  exact ⟨TGen.pick tx ty, by ext; rfl⟩

@[simp, aesop safe (rule_sets := [totality])]
theorem total_map
    (hx : total x) :
    total (f <$> x) := by
  obtain ⟨tx, rfl⟩ := hx
  exact ⟨TGen.map f tx, by ext; rfl⟩

@[simp, aesop safe (rule_sets := [totality])]
theorem total_dite
    {g₁ : b = true → Gen α}
    {g₂ : ¬ (b = true) → Gen α}
    (h₁ : (h : b = true) → total (g₁ h))
    (h₂ : (h : ¬(b = true)) → total (g₂ h))
    : total (if h : b then g₁ h else g₂ h) := by
  by_cases hb : b = true
  · rw [dif_pos hb]; exact h₁ hb
  · rw [dif_neg hb]; exact h₂ hb

/- Recursion has no generic totality lemma: each datatype's `unfold` gets its own `X.total_unfold`
in `Palamedes/Data/`, whose witness is that datatype's `unfold` re-run at the failure-free interface
(`TGen`). Because the unfold body never mentions `Fail`, the witness equality is a fixpoint
congruence — see `List.total_unfold`. -/

end Total

end Gen

end Palamedes
