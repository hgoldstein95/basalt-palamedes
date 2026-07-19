# Palamedes

Palamedes is a Lean 4 library that synthesizes random generators from logical predicates. Given a
predicate `P : α → Prop` (or a decidable `α → Bool`), the `generator_search` tactic produces a `Gen
α` whose *support* is exactly `P` — it can produce every value satisfying `P` and nothing else.
Synthesis runs at elaboration time, inside a proof, driven by
[Aesop](https://github.com/leanprover-community/aesop).

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
CI runs) also runs the tests. Note that a **totality-check failure is a warning, not an error** —
grep the build output for warnings, or you will miss it.

Beyond the corpus, each file in `PalamedesTest/` guards one library module and is named after it —
`PalamedesTest/Foo.lean` guards `Palamedes/Foo.lean`, so the two directory listings diff into a
coverage map. The ones worth knowing about:

- **`Extract.lean`** walks every generator in the corpus and fails the build if synthesis
  residue (`Subtype.val`, `Eq.mpr`, `CorrectGen`, or a bare `Gen.pick`) survived into the compiled
  term.
- **`Derive.lean`** pins the signatures `derive_palamedes` generates, and `#print axioms` on the
  proofs it emits.
- **`Stats.lean`** and **`Optimizer/Schedule.lean`** pin `#genstats` distribution reports
  under `#guard_msgs` — respectively, that the optimizer's flatten pass really does produce a
  *uniform* choice, and that depth schedules really do make a recursive generator terminate.

`PalamedesExamples/` is teaching material with no assertions; `PalamedesExperiments/` holds
exploratory spikes and is excluded from the default build.

## Usage

Import `Palamedes` (or just `Palamedes.Synthesizer` for the tactic alone) and call
`generator_search` with a predicate:

```lean4
import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

def genEq2 : Gen Nat := by
  generator_search (· = 2)
```

The predicate may also be a recursive decidable property over a supported datatype:

```lean4
@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

def genAllTwos : Gen (List Nat) := by
  generator_search (fun xs => isAllTwos xs)
```

Useful variants:

- `generator_search? P` also emits the synthesized term as a "Try this" suggestion, so you can see
  (and paste) what the search actually produced.
- `generator_search P allow_partial` skips the *totality check*, admitting a generator that still
  *filters* — one containing a `Gen.assume` that can fail. Needed by `genAVL` and `genRBT`.
- `generator_search P with_policy` turns on depth-indexed weight schedules, which make a
  recursive generator's branching subcritical so that it terminates in practice. Use it for a
  generator whose seed does not shrink (`genWellTyped` diverged on 54.3% of draws without it); leave
  it off for one whose seed does (`genBST`, `genLengthK`), where decay would only shrink the
  outputs. See the `generator_search` docstring for the full story.

To draw values, import `Palamedes` (which re-exports both the tactic and the sampler):

```lean4
import Palamedes

#eval Palamedes.sampleN 10 genAllTwos   -- draw 10 values
#eval Palamedes.sample genAllTwos       -- draw one
```

Both take an optional `size`. **The sampler has no fuel and no backtracking**: an `allow_partial`
generator can throw when a draw hits its failing branch, and a generator that is not almost-surely
terminating can hang. See the module docstring in `Palamedes/Sample.lean`.

To inspect a generator's *distribution* rather than a few samples, import `Palamedes.Stats` and use
Basalt's `#genstats` command: `#genstats (toStatGen (genBST 0 10))`.

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

- **`Palamedes/Gen.lean`** — the core types. `Gen α` is a *structure* wrapping a polymorphic Basalt
  generator (`∀ {G} [Gen G] [Fail G], G α`), with combinators `pure`/`>>=`/`pick`/`oneOf`/
  `frequency`/`assume`/`empty`. `support g := SPMF.support g.run` is the set of values it can
  produce. `TGen` is the same thing *without* the `Fail` capability, which makes "never filters" the
  structural fact "typeable without `Fail`" — that is `Gen.total`. (Totality is assume-freedom, *not*
  termination; the two are orthogonal.)
- **`Palamedes/CorrectGen.lean`** — `CorrectGen P := {g : Gen α // g.support = P}`, a generator
  bundled with a proof that its support is exactly `P`, plus the combinators the search composes.
  Synthesis is a proof search for an inhabitant of this.
- **`Palamedes/Derive.lean`** — the `derive_palamedes` command (see above). This is where the
  recursion scheme lives, in exactly one place, so a change to it reaches every datatype at once.
- **`Palamedes/Synthesizer/`** — the five-stage pipeline. `CGeneratorSearch.lean` registers the
  synthesis rules with Aesop and defines `cgenerator_search`; `FrontEnd.lean` defines the user-facing
  `generator_search` (search → extract a raw `Gen` → optimize → check totality → close the goal);
  `Totality.lean` reconstructs the `TGen` witness.
- **`Palamedes/Extract.lean`** and **`Optimizer.lean`** — stages 2 and 3. Extraction is the `extract`
  simp set (one `.val` equation per synthesis combinator), which pulls the raw `Gen` out of the
  `CorrectGen` term. The optimizer is a **proof-carrying** rewriter: every rewrite composes a
  support-preservation proof, which is type-checked before the goal is closed. Three passes: monad
  laws and assume-floating, then collapsing `pick` trees into uniform `oneOf`s, then — only under
  `with_policy` — installing depth-indexed weights. `Support.lean` holds the proof-side twin
  lemma for each rewrite.
- **`Palamedes/Total.lean`** — `TGen`, `Gen.total`, and the combinator-wise totality lemmas that
  stage 4 reconstructs a witness from.
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
