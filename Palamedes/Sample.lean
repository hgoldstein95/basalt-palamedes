import Palamedes.Gen
import Basalt.PlausibleGen
import Plausible

/-!
# Executable sampling for Palamedes generators

A `Palamedes.Gen α` is a thin wrapper around a polymorphic Basalt generator
(`∀ {G} [Gen G], G α`). Basalt provides a `Gen Plausible.Gen` instance (`Basalt.PlausibleGen`), so we
sample by instantiating the generator at `Plausible.Gen` and running it with Plausible's sampler.

The filtering combinators (`Gen.assume`/`Gen.empty`) bottom out at the `Fail` capability's `fail`.
The `Fail Plausible.Gen` instance below interprets that as a thrown `GenError` (via Plausible's
`MonadExcept`) — a *computable* failure, so filtered generators can be sampled.

## Known limitation: no fuel or backtracking (deferred)

This is a deliberately minimal sampler: it does **not** bound recursion depth or retry on failure —
Basalt's `Plausible.Gen` interpretation of `pick` commits to one branch, and a thrown `Fail`
propagates straight out. Two consequences:

* **Filtering generators can fail outright.** A generator synthesized with `allow_partial` (so it
  contains a genuinely failing `assume`) throws `GenError` whenever a random path hits the failing
  branch, with no backtracking to recover (e.g. `genAVL`, `genRBT`).
* **Recursion can diverge.** `total` here means *assume-free*, not *terminating* (almost-sure
  termination, `SPMF.IsPMF`, is a separate property the synthesizer does not yet establish). A total
  but non-a.s.-terminating generator — typically branching recursion with no size decay — can fail to
  terminate when sampled (e.g. `genWellTyped`).

Generators that are both non-filtering and a.s.-terminating (e.g. `genBST`, `genSortedBetween`,
`genWellScoped`) sample fine. A size-bounded / backtracking sampler is left as future work.
-/

namespace Palamedes

open Gen

/-- Computable failure for the executable interpretation: a thrown generation error. (Note that the
sampler does not catch it — see the module docstring's "Known limitation".) -/
instance : Fail Plausible.Gen := ⟨throw Plausible.Gen.genericFailure⟩

/-- Interpret `g` at Plausible's `Gen` monad. -/
def toPlausible (g : Gen α) : Plausible.Gen α := g.run

/-- Draw a single value from `g` at the given size. -/
def sample (g : Gen α) (size : Nat := 100) : IO α :=
  Plausible.Gen.run (toPlausible g) size

/-- Draw `n` values from `g`. -/
def sampleN (n : Nat) (g : Gen α) (size : Nat := 100) : IO (List α) :=
  (List.replicate n ()).mapM (fun _ => sample g size)

end Palamedes
