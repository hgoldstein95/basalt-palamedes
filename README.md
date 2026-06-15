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

The toolchain is pinned in `lean-toolchain` (Lean `v4.30.0`). Dependencies — MathLib, Aesop, and
Plausible — are pinned in `lakefile.toml` / `lake-manifest.json`.

## Building

```sh
lake build                                       # build the library and the full example corpus
lake build Palamedes                             # build just the library
lake build PalamedesTest.Examples.Simple.Eq2     # build/elaborate a single example (module path)
lake build InProgress                            # build the known-failing WIP corpus (expected to fail)
```

There is no separate test framework. Every file under `PalamedesTest/Examples/` synthesizes a
generator at elaboration time and fails to compile if synthesis fails, so a plain `lake build` (what
CI runs) also runs the tests. `PalamedesTest/ExtractionAudit.lean` additionally guards against
silent extraction failures by checking that no synthesis residue survives in the compiled
generators.

## Usage

Import `Palamedes.Synthesizer` and call `generator_search` with a predicate:

```lean4
import Palamedes.Synthesizer

open Gen CorrectGen

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

- `generator_search? P` emits the synthesized term as a suggestion (so it can be pasted in place of
  the tactic call).
- `generator_search P allow_partial` skips the _totality check_, which allows generators that may
   need to backtrack at sample time.

To draw values, import `Palamedes.Sample` (or the `Palamedes` root, which re-exports both the tactic
and the sampler) and interpret a `Gen` as a runnable sampler on top of Plausible:

```lean4
import Palamedes

-- draw 10 values from genAllTwos
#eval Gen.sampleN 10 genAllTwos
```

`Gen.sample` draws a single value, and `SampleConfig` controls size and backtracking behavior.

## Layout

- **`Palamedes/Gen.lean`** — the `Gen` type (an inductive: `ret`, `bind`, `pick`, `indexed`,
  `assume`) and `support : Gen α → α → Prop`, the set of values a generator can produce, plus
  `simp` lemmas describing how `support` distributes over each constructor. `Support.lean` adds
  further `support` rewriting lemmas.
- **`Palamedes/CorrectGen.lean`** — `CorrectGen P := {g : Gen α // g.support = P}`, a generator
  bundled with a proof that its support equals the target predicate, along with the basic synthesis
  rules that combine `CorrectGen`s.
- **`Palamedes/Synthesizer/`** — `CGeneratorSearch.lean` registers the synthesis rules with Aesop
  and defines the `cgenerator_search` tactic; `FrontEnd.lean` defines the user-facing
  `generator_search` tactic (search, extract a raw `Gen`, optimize, re-prove support, and prove
  totality); `Totality.lean` proves generators never need to backtrack.
- **`Palamedes/Extract.lean`** and **`Optimizer.lean`** — extracting a plain `Gen` out of a
  `CorrectGen` term and simplifying it (monad laws, bind reassociation), with the `optimality`
  tactic re-proving that support is preserved.
- **`Palamedes/Sample.lean`** — interprets a `Gen` as a runnable sampler with backtracking and size
  configuration (`SampleConfig`).
- **`Palamedes/Data/`** — per-datatype machinery the synthesizer needs (base functors, recursion
  schemes, synthesis and case-analysis rules, support/termination lemmas). Covered types: `Nat`,
  `Bool`, `Unit`, `Color`, `Tuple`, `List`, `Tree`, `Stack/`, and `STLC/`. Adding support for a new
  recursive datatype means adding a `Data/` module of this shape and importing it in
  `CGeneratorSearch.lean`.
- **`Palamedes/RuleSets.lean`** and **`Util.lean`** — the central Aesop rule-set declarations and
  shared meta-level helpers.
- **`PalamedesTest/Examples/`** — the example corpus. `Simple/` and `Range/` are the easiest
  starting points; each datatype directory also has examples using the harder, more general "unfold
  strategy" from the paper. `InProgress/` holds cases that do not yet synthesize.
