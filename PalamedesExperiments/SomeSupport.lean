import Palamedes.SomeSupport

/-!
# The `someSupport` obstruction

**This experiment has landed.** `someSupport`, the `OptionT` lemma kit, the combinator twins and the
per-datatype `X.someSupport_unfold` all live in `Palamedes/SomeSupport.lean` and
`Palamedes/Derive.lean` now; `correct def` emits `f.sound_complete : IsSomeSoundAndComplete f P` for
a filtering generator. What follows is the one statement that did *not* land, kept here because it
is the boundary of what the approach can reach.

Two things the probe got wrong, worth remembering when estimating the next one:

* It checked `pure`/`bind`/`pick`/`assume` and the `unfold` twin, and concluded the combinator kit
  was three lemmas. But the **optimizer** emits `frequency`/`oneOf` — it flattens `pick` chains — and
  those were never exercised. `frequencyAux` is a `choose`-then-`dite` whose dead `else` branch is
  `default`, and `OptionT SPMF α`'s `Inhabited` (`pure none`) is a different term from
  `SPMF (Option α)`'s, so `OptionT.run` does not distribute over `frequency` without a `0 < total`
  hypothesis to kill the branch. That is `run_frequencyAux`, and it was the bulk of the work.
* It measured the *emitter* change, which was indeed ~30 lines and worked first try, and did not
  measure the **leaf lemma inventory** — the seven hand-written primitives (`arbNat`, `arbBool`,
  `arbColor`, `choose`, `lt`, `gt`, `mod2`) each needing a twin next to their `support_` lemma.

A probe that samples the library's own combinators, rather than the ones the optimizer emits,
measures the wrong thing.
-/

namespace Palamedes

variable {α : Type}

/-- **Not provable.** `g.run` is an arbitrary element of `∀ {G} [Gen G] [Fail G], G α`; relating its
`SPMF` instance to its `OptionT SPMF` instance is a parametricity (free-theorem) statement about
that Π-type. Lean's logic is compatible with non-parametric inhabitants (there is no internal
relational interpretation available), so this needs *either* a parametricity axiom *or* replacing
`Gen`'s carrier by an inductive syntax of generators, with the combinator twins in
`Palamedes/SomeSupport.lean` as its cases. Difficulty: not a proof-engineering problem, a
foundational one.

Nothing in the shipped filtering path depends on it. `correct def` discharges the *instance* it
needs — `someSupport g = g.support` for the one generator it just synthesized — by `simp` over the
combinator twins, which is available precisely because that `g` is a concrete term built from the
basis rather than an opaque one. This lemma is what would make the per-datatype and per-primitive
twins unnecessary, not what makes them sound. -/
theorem parametricity (g : Gen α) : someSupport g = g.support := by
  sorry

end Palamedes
