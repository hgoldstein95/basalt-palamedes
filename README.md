# Palamedes

Palamedes is a Lean 4 library that synthesizes random generators from logical predicates. Given a
predicate `P : α → Prop` (or a decidable `α → Bool`), the `generator_search` tactic produces a
[Basalt](https://github.com/hgoldstein95/basalt) generator whose *support* is exactly `P`: it can
produce every value satisfying `P` and nothing else.
Synthesis runs at elaboration time, inside a proof, driven by
[Aesop](https://github.com/leanprover-community/aesop).

While this project has evolved quite a bit over time, it is still largely based on
[The Search for Constrained Random Generators](https://dl.acm.org/doi/abs/10.1145/3808329),
published at PLDI 2026. The original GitHub repository for that code can be
found [here](https://github.com/hgoldstein95/palamedes-lean/).

Users should be aware that this is research software. We are working hard to make it increasingly
stable and flexible, but you may still run into snags when using it.

## Requirements

Palamedes is built on [Basalt](https://github.com/hgoldstein95/basalt), which supplies the generator
representation it synthesizes onto: the `Gen` typeclass, the `SPMF` (sub-probability mass function)
interpretation that gives `support` its meaning, the executable `Plausible.Gen` instance, and the
`#genstats` diagnostics command. Basalt is a git dependency **tracking `main`**, with the revision
pinned in `lake-manifest.json`; run `lake update basalt` to pick up new Basalt work.

## Building

The repository should simply build with Lake.

```sh
lake exe cache get
lake build
```

## Usage

Import `Palamedes` and call `generator_search` with a predicate:

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

If you want to actually see the generator, use `generator_search?`.

### Potentially Failing Generators

Palamedes always attempts to produce non-backtracking generators, but sometimes backtracking is
necessary. If `generator_search` fails with an error that the search could not find a
non-backtracking generator, you can opt in to a potentially failing generator by changing the type
of the synthesized value:

```lean4
def genBetween (lo hi : Nat) [Gen G] : G (Option Nat) := by
  generator_search (fun n => lo ≤ n ∧ n ≤ hi)
```

The above generator either successfully samples `some n` where `lo ≤ n ∧ n ≤ hi` or else returns
`none`.

### Keeping Proofs

The Palamedes synthesis process produces a number of proofs that the generator it synthesizes is
appropriate. If you want to keep those proofs around, add the `@[correct]` attribute.

```lean4
@[correct]
def genAllTwosLawful [Gen G] : G (List Nat) := by
  generator_search (fun xs => isAllTwos xs)

-- info: @[correct] genAllTwosLawful: emitted sound_complete
-- genAllTwosLawful.sound_complete : IsSoundAndComplete genAllTwosLawful fun xs => isAllTwos xs = true
```

### Adding Tuning Parameters

A Palamedes generator is guaranteed to produce the correct *support* but it may not produce an ideal
*distribution*. You can use `generator_search?` to print the generator to the file, at which point
you can tune it manually, but we can also make that process a bit more automatic.

Adding an argument of type `Tuning` to your generator signature causes `generator_search` to add
parameterized weights to the synthesized generator. For example:

```lean4
def genWellTyped (Γ : List Ty) (θ : Tuning) [Gen G] : G Term := by
  generator_search (fun t => isWellTyped Γ t)

-- Actually tune the generator with a particular policy:
#genstats (genWellTyped [] (SchedulePolicy.stlc.materialize genWellTyped.sites))
```

When a `Tuning` parameter is added, the synthesizer also emits a `.sites` definition, which tracks
the different tuning sites in the generator, along with a default `SchedulePolicy`.

We plan to release a more comprehensive tutorial on tuning, but for now you can learn more in
`Palamedes/Tuning.lean`.

### Sampling Values

You can draw values from a generator the same way that you can with any Basalt generator --- by
interpreting the generator at `Plausible.Gen` or `IO`.

```lean4
#eval Plausible.Gen.run genAllTwos 10               -- G α: a Plausible generator already
#eval Palamedes.samplePartialN 10 (genBetween 3 7)  -- G (Option α): draw through the retry loop
```

To inspect a generator's distribution, use Basalt's `#genstats` command.

## Deriving Infrastructure for Inductive Types

If you have your own inductive type that you'd like to use with Palamedes, use the
`derive_palamedes` command:

```lean4
derive_palamedes MyTree
```

This command generates definitions that Palamedes needs to work with predicates and generators over.
The command works with many inductive types, but not all: we reject mutual, nested, and indexed
inductives.

For primitive types, especially finite enumerations, where the only generator
you actually need is a single "arbitrary" generator, we provide a shortcut
command, `derive_enum_gen`:

```lean4
inductive MyColor
  | Black
  | White

derive_enum_gen MyColor
```

This produces `arbMyColor` that uniformly chooses between constructors, without
the other infrastructure.

## Testing

The main test for this repository is the corpus of test examples (largely drawn from the PLDI
paper).  Every file under `PalamedesTest/Corpus/` synthesizes a generator at elaboration time and
fails to compile if synthesis fails.

Beyond the corpus, each file in `PalamedesTest/` guards one library module and is named after it —
`PalamedesTest/Foo.lean` guards `Palamedes/Foo.lean`, so the two directory listings diff into a
coverage map. The exceptions are `GeneratorAPI.lean`, `TotalWitness.lean`, and `Stats.lean`, which
have no library counterpart and are named for what they pin, and `Harness.lean`, which holds the
assertions the audit modules share.

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
- **`Palamedes/Derive/`** — the `derive_palamedes` and `derive_enum_gen` commands (see above),
  split into the input check (`Analyze`), the base functor, the recursion schemes and their laws,
  and the fusion family. This is where the recursion scheme lives, in exactly one place, so a change
  to it reaches every datatype at once.
- **`Palamedes/Synthesizer/`** — the five-stage pipeline. `CGeneratorSearch.lean` registers the
  synthesis rules with Aesop and defines `cgenerator_search`; `FrontEnd.lean` defines the user-facing
  `generator_search` (search → extract a raw `PGen` → optimize → check totality → close the goal);
  `Totality.lean` reconstructs the `TGen` witness.
- **`Palamedes/Extract.lean`** and **`Palamedes/Optimizer.lean`** — stages 2 and 3. Extraction is the `extract`
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
- **`Palamedes/Laws.lean`** and **`Palamedes/SomeSupport.lean`** — the bridges from Palamedes'
  `support` facts to the emitted laws: Basalt's `IsSoundAndComplete`, plus the filtering path's
  `IsSomeSoundAndComplete` — Palamedes' own notion, defined in `Laws.lean` since Basalt has no
  filtering law — and the `OptionT SPMF` twin lemmas it is discharged by.
- **`Palamedes/Synthesizer/Correct.lean`** — the `@[correct]` attribute: the tactic stashes the
  pipeline's proofs, and the attribute — running once the constant exists — `addDecl`s them as named
  theorems about it.
- **`Palamedes/Sample.lean`** — running a *filtering* generator: the retry loop on top of Plausible
  that redraws a `none`. A total one is a Basalt generator and needs nothing from here, and
  distribution reports are Basalt's own `#genstats` at either shape.
- **`Palamedes/Data/`** — the supported datatypes. The recursive ones (`List`, `Tree`, `Stack`, and
  the STLC `Ty`/`Term`) are largely a `derive_palamedes` line plus the odd fusion lemma the command
  does not yet emit. The hand-written content is the primitives the synthesizer bottoms out at
  (`Nat`, `Bool`, `Unit`, `Color`, `Tuple`, `Stack/Atom`, `List/Elements`) and, in `STLC/Ty.lean`, a
  hand-tuned `arbTy` and its case-analysis rules on top of the derived layer.
- **`Palamedes/Util.lean`** — two meta-level tactics (`rflm`, `unfold_matches`) shared by the
  synthesizer and the derive command.
- **`Palamedes/RuleSets.lean`**, **`Palamedes/CaseSplit.lean`**, **`Palamedes/OptimizeCongr.lean`**,
  **`Palamedes/UnfoldStrategy.lean`** — the registries. Each is an attribute or environment extension that
  lets a datatype or a lemma opt into a stage of the pipeline by being *tagged*, rather than by being
  named in a list inside the synthesizer. This is what makes "adding a datatype is one line" true.
