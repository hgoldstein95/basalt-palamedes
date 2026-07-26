# Palamedes

Palamedes is a Lean 4 library that synthesizes random generators from logical predicates. Given a
predicate `P : α → Prop` (or a decidable `α → Bool`), the `generator_search` tactic produces a
generator — in [Basalt](https://github.com/hgoldstein95/basalt)'s own shape, `[Gen G] → G α` —
whose *support* is exactly `P`: it can produce every value satisfying `P` and nothing else.
Synthesis runs at elaboration time, inside a proof, driven by
[Aesop](https://github.com/leanprover-community/aesop), and the `@[correct]` attribute keeps the
support fact as a named theorem.

This is research code accompanying a [PLDI 2026 paper](https://dl.acm.org/doi/abs/10.1145/3808329).
The core pipeline works, but there are rough edges and all APIs should be considered unstable. We
will read issues that are posted, but make no promises about how quickly they will be addressed.

## Requirements

The toolchain is pinned in `lean-toolchain`. Dependencies are pinned in `lakefile.toml` /
`lake-manifest.json`.

Palamedes is built on [Basalt](https://github.com/hgoldstein95/basalt), which supplies the generator
representation it synthesizes onto: the `Gen` typeclass, the `SPMF` (sub-probability mass function)
interpretation that gives `support` its meaning, the executable `Plausible.Gen` instance, and the
`#genstats` diagnostics command. Basalt is a git dependency **tracking `main`**, with the revision
pinned in `lake-manifest.json`; run `lake update basalt` to pick up new Basalt work.

## Building

```sh
lake build                                     # build the library, the examples and the tests
lake build Palamedes                           # build just the library
lake build PalamedesTest                       # build just the tests
lake build PalamedesTest.Corpus.Simple.Eq2     # build/elaborate a single example (module path)
```

There is no separate test framework. Every file under `PalamedesTest/Corpus/` synthesizes a
generator at elaboration time and fails to compile if synthesis fails, so a plain `lake build` (what
CI runs) also runs the tests. Note that a totality-check failure is an **error** for a generator
declared `G α` (there is no term to emit) but only a **warning** for the synthesis-internal
`Palamedes.PGen α` shape — grep the build output for warnings, or you will miss the latter.

Beyond the corpus, each file in `PalamedesTest/` guards one library module and is named after it —
`PalamedesTest/Foo.lean` guards `Palamedes/Foo.lean`, so the two directory listings diff into a
coverage map. The ones worth knowing about:

- **`Extract.lean`** walks every generator in the corpus (both shapes — Basalt-shaped and the
  internal carrier) and fails the build if synthesis residue (`Subtype.val`, `Eq.mpr`, `CorrectGen`,
  a totality-witness constructor, or a bare `PGen.pick`) survived into a compiled term's data path.
- **`Derive.lean`** pins the signatures `derive_palamedes` generates, and `#print axioms` on the
  proofs it emits.
- **`Stats.lean`** and **`Optimizer/Schedule.lean`** pin `#genstats` distribution reports
  under `#guard_msgs` — respectively, that the optimizer's flatten pass really does produce a
  *uniform* choice, and that depth schedules really do make a recursive generator terminate.

`PalamedesExperiments/` holds exploratory spikes and is excluded from the default build.

## Usage

Import `Palamedes` and call `generator_search` with a predicate. The generator you get is a
Basalt generator — Basalt's own tooling consumes it with no adapter:

```lean4
import Palamedes

def genEq2 [Gen G] : G Nat := by
  generator_search (· = 2)
```

The predicate may also be a recursive decidable property over a supported datatype:

```lean4
@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

def genAllTwos [Gen G] : G (List Nat) := by
  generator_search (fun xs => isAllTwos xs)
```

**The declared return type says whether the generator can fail.** A generator that *filters* — one
whose synthesis leaves a `PGen.assume` that can reject a draw — must be declared at `G (Option α)`;
declaring it at `G α` is an error naming that fix. This is a fact about the type, visible at every
use site:

```lean4
def genBetween (lo hi : Nat) [Gen G] : G (Option Nat) := by
  generator_search (fun n => lo ≤ n ∧ n ≤ hi)
```

`@[correct]` **keeps the proofs**: the generator is exactly the one you would get without it, plus
`genFoo.sound_complete` — the support fact, in Basalt's law vocabulary. It reports what it emitted,
so a missing law is something you read rather than assume:

```lean4
@[correct] def genAllTwosLawful [Gen G] : G (List Nat) := by
  generator_search (fun xs => isAllTwos xs)
-- info: @[correct] genAllTwosLawful: emitted sound_complete
-- genAllTwosLawful.sound_complete : IsSoundAndComplete genAllTwosLawful fun xs => isAllTwos xs = true
```

It is an ordinary attribute, so it composes: it sits beside any other attribute, and it works with
`generator_search?` below.

**Weighting is part of the signature.** Give a generator a `Tuning` binder and every choice site
reads it; leave it out and the generator ships uniform. There is no separate command and no flag —
the declared type says whether a generator is tunable, the same way it says whether one can fail:

```lean4
def genWellTyped (Γ : List Ty) (θ : Tuning := .uniform) [Gen G] : G Term := by
  generator_search (fun t => isWellTyped Γ t)

#genstats (genWellTyped [] (SchedulePolicy.stlc.materialize genWellTyped.sites))
```

`genFoo.sites` is emitted alongside the generator, and a `SchedulePolicy` is materialized against
it. `.uniform` is a universal default — `Tuning.weight` falls back to `(1, 0)` for any index — so
the untuned call mentions tuning nowhere. Support is unaffected by the weighting *for every* `θ`,
and because `θ` is one of the declaration's own binders that is the ordinary `genFoo.sound_complete`
rather than a second law. Depth-*decaying* weights are what make a recursive generator whose seed
does not shrink terminate in practice (`genWellTyped` diverged on 54.3% of draws uniform); see
`SchedulePolicy` in `Palamedes/Schedule.lean`.

Other variants: `generator_search? P` also emits the synthesized term as a "Try this" suggestion,
so you can see (and paste) what the search actually produced.

There is a third declarable shape, `Palamedes.PGen α` — the synthesis carrier, and the semantic
object the library's proofs are about (`support g := SPMF.support g.run`). Declare it when you want
to reason about `support` directly rather than through Basalt's `IsSoundAndComplete`; `@[correct]`
then emits `genFoo.total` alongside `genFoo.sound_complete`, stated at Palamedes' own vocabulary.
It is not the shape to reach for otherwise: it is not a Basalt generator, so everything downstream
needs an adapter, and where a Basalt `G α` makes a totality failure an error the carrier can only
warn — and `lake build` exits 0 on warnings.

```lean4
@[correct] def genAllTwosCarrier : Palamedes.PGen (List Nat) := by
  generator_search (fun xs => isAllTwos xs)
-- info: @[correct] genAllTwosCarrier: emitted sound_complete, total
-- genAllTwosCarrier.sound_complete : genAllTwosCarrier.support = fun xs => isAllTwos xs = true
```

To draw values:

```lean4
#eval Plausible.Gen.run genAllTwos 10               -- G α: a Plausible generator already
#eval Palamedes.samplePartialN 10 (genBetween 3 7)  -- G (Option α): draw through the retry loop
#eval Palamedes.sampleN 10 genAllTwosCarrier        -- Palamedes.PGen α: via `totalize`, then the loop
```

A `G α` needs nothing from Palamedes to run — Basalt's `Gen Plausible.Gen` instance makes it a
`Plausible.Gen`, and the second argument is Plausible's `size`. The other two go through
`Palamedes/Sample.lean`, which redraws a failed draw (a filtering generator rejecting) up to
`maxAttempts` times, so filtering samples rather than throwing. But **there is no fuel against
divergence**: a generator that is not almost-surely terminating can hang. See that module's
docstring.

To inspect a generator's *distribution* rather than a few samples, use Basalt's `#genstats` command.
Both Basalt shapes are consumed directly, no adapter: `#genstats (draws := 30) genAllTwos`; a
`Palamedes.PGen`-shaped one goes through `toStatGen` (`import Palamedes.Stats`).

## Adding a datatype

One line:

```lean4
derive_palamedes MyTree
```

`derive_palamedes` generates the entire per-datatype layer — base functor, `fold`, `accuM`,
the `unfold` recursion scheme, its support and totality lemmas, the fold/`accuM` fusion lemmas — and
registers the result with the synthesizer. **No edit to any `Palamedes/` module is needed.**
`PalamedesTest/Corpus/LeafTree/` is the end-to-end proof of that: it declares a datatype the
library has never heard of, inside a test file, and synthesizes for it. Debug with
`set_option trace.Palamedes.derive true`.

Rejected by design, loudly: mutual, nested, and indexed inductives. (A rose tree — `node : List
(Tree α) → Tree α` — is the canonical unsupported shape.)

## Layout

- **`Palamedes/PGen.lean`** — the core types. `PGen α` is a *structure* wrapping a polymorphic Basalt
  generator (`∀ {G} [Gen G] [Fail G], G α`), with combinators `pure`/`>>=`/`pick`/`oneOf`/
  `frequency`/`assume`/`empty`. `support g := SPMF.support g.run` is the set of values it can
  produce. `TGen` is the same thing *without* the `Fail` capability, which makes "never filters" the
  structural fact "typeable without `Fail`" — that is `PGen.total`. (Totality is assume-freedom, *not*
  termination; the two are orthogonal.)
- **`Palamedes/CorrectGen.lean`** — `CorrectGen P := {g : PGen α // g.support = P}`, a generator
  bundled with a proof that its support is exactly `P`, plus the combinators the search composes.
  Synthesis is a proof search for an inhabitant of this.
- **`Palamedes/Derive.lean`** — the `derive_palamedes` command (see above). This is where the
  recursion scheme lives, in exactly one place, so a change to it reaches every datatype at once.
- **`Palamedes/Synthesizer/`** — the five-stage pipeline. `CGeneratorSearch.lean` registers the
  synthesis rules with Aesop and defines `cgenerator_search`; `FrontEnd.lean` defines the user-facing
  `generator_search` (search → extract a raw `PGen` → optimize → check totality → close the goal);
  `Totality.lean` reconstructs the `TGen` witness.
- **`Palamedes/Extract.lean`** and **`Optimizer.lean`** — stages 2 and 3. Extraction is the `extract`
  simp set (one `.val` equation per synthesis combinator), which pulls the raw `PGen` out of the
  `CorrectGen` term. The optimizer is a **proof-carrying** rewriter: every rewrite composes a
  support-preservation proof, which is type-checked before the goal is closed. Two passes: monad
  laws and assume-floating, then collapsing `pick` trees into uniform `oneOf`s. `Support.lean` holds
  the proof-side twin lemma for each rewrite.
- **`Palamedes/Tuning.lean`** — `installTuning`, the pipeline stage between optimize and totality:
  rewrites a generator's `oneOf`s into `frequency`s reading the declaration's `Tuning` binder, and
  proves the support unchanged for every `θ`. Running *inside* the pipeline is what makes one
  generator, one witness and one law suffice at every shape.
- **`Palamedes/Total.lean`** — `TGen`, `PGen.total` (`Type`-valued: the totality witness *is* the
  failure-free generator the Basalt shape is projected from), and the combinator-wise totality
  lemmas that stage 4 reconstructs a witness from.
- **`Palamedes/Laws.lean`** and **`SomeSupport.lean`** — the bridges from Palamedes' `support` facts
  to Basalt's law vocabulary (`IsSoundAndComplete`), including the filtering path's
  `IsSomeSoundAndComplete` and the `OptionT SPMF` twin lemmas it is discharged by.
- **`Palamedes/Synthesizer/Correct.lean`** — the `@[correct]` attribute: the tactic stashes the
  pipeline's proofs, and the attribute — running once the constant exists — `addDecl`s them as named
  theorems about it.
- **`Palamedes/Sample.lean`** and **`Stats.lean`** — running a generator: as an executable sampler on
  top of Plausible, and as a distribution report via Basalt's `#genstats`.
- **`Palamedes/Data/`** — the supported datatypes. The recursive ones (`List`, `Tree`, `Stack`, and
  the STLC `Ty`/`Term`) are largely a `derive_palamedes` line plus the odd fusion lemma the command
  does not yet emit. The hand-written content is the primitives the synthesizer bottoms out at
  (`Nat`, `Bool`, `Unit`, `Color`, `Tuple`, `Stack/Atom`, `STLC/Context`) and, in `STLC/Ty.lean`, a
  hand-tuned `arbTy` and its case-analysis rules on top of the derived layer.
- **`Palamedes/Util.lean`** — two meta-level tactics (`rflm`, `unfold_matches`) shared by the
  synthesizer and the derive command.
- **`Palamedes/RuleSets.lean`**, **`CaseSplit.lean`**, **`OptimizeCongr.lean`**,
  **`UnfoldStrategy.lean`** — the registries. Each is an attribute or environment extension that
  lets a datatype or a lemma opt into a stage of the pipeline by being *tagged*, rather than by being
  named in a list inside the synthesizer. This is what makes "adding a datatype is one line" true.
- **`PalamedesTest/Corpus/`** — the corpus. `Simple/` and `Range/` are the easiest starting points.
  Each datatype directory generally carries two spellings of the same predicate: a structurally
  recursive one (`BST.lean`) and one written as an explicit catamorphism (`Fold.lean`). These are not
  duplicates — they exercise different paths through the search.
