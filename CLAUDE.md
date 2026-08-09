# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

Palamedes is a Lean 4 library that **synthesizes random generators from logical predicates**. Given
`P : α → Prop` (or decidable `α → Bool`), the `generator_search` tactic produces a
[Basalt](https://github.com/hgoldstein95/basalt) generator (`[Gen G] → G α`) whose *support* is
exactly `P`. Synthesis happens at elaboration time, inside a proof, driven by Aesop. Research code
for a PLDI 2026 paper; APIs are unstable.

`README.md` is the user-facing reference and is kept accurate — read it before changing public
behavior, and update it when you do.

## Commands

```sh
lake build                                     # library + tests (what CI runs)
lake build Palamedes                           # library only
lake build PalamedesTest                       # tests only
lake build PalamedesTest.Corpus.Simple.Eq2     # one corpus file, by module path
lake env lean PalamedesTest/Corpus/Simple/Eq2.lean   # elaborate one file, see all messages
lake build PalamedesExperiments                # spikes; excluded from the default build
lake update basalt                             # re-resolve the Basalt release tag set in lakefile.toml
```

**There is no separate test framework.** Every module under `PalamedesTest/Corpus/` synthesizes a
generator at elaboration time and fails to compile if synthesis regresses, so `lake build` *is* the
test suite. Many corpus files additionally pin the **emitted term** with `generator_search?`
under `#guard_msgs`, so a search that still succeeds but finds a *different* generator is a build
failure rather than a silent change. To regenerate one, edit nothing but the docstring: delete it,
run `lake env lean <file>`, paste the output back under `info:`.

A pin is only half the contract — the emitted term also has to *re-elaborate* when pasted, which no
`#guard_msgs` checks. `Corpus/List/IdxOf/` is the one that does, by declaring the pinned text a
second time as an ordinary `def`. Do that whenever a change touches how side-condition proofs print:
`delabDroppingProof` drops a proof only when the combinator's autoParam can rebuild it, and a
delaborator that gets that judgement wrong produces a term that pins fine and does not compile.

**Read that diff before regenerating it.** A *larger* emitted term is the regression, not the new
golden — it usually means rule order shifted and the search found a worse generator, which then
blows `maxRecDepth` somewhere downstream. BST is the natural canary. RBT and BadRBT are deliberately
*not* term-pinned (their emitted terms are long enough that the diff stops being readable);
`PalamedesTest/Stats.lean` pins their `#genstats` reports instead.

**Wall-clock build time is a first-class metric.** Several corpus files already run near their
limits, raising `maxHeartbeats` (and sometimes `maxRecDepth`) in their own headers —
`grep -rn maxHeartbeats PalamedesTest/Corpus` lists which, and each file's budget is set there.
Compare build times across any synthesizer change.

**Warnings hide real failures.** `lake build` exits 0 on warnings, and synthesis emits two kinds: a
generator declared `G (Option _)` that turns out never to fail, and a reconstruction *gap* under
that same shape — where `totalize` accepts the generator either way, so the missing `@[total]` rule
stays buried behind an `Option` nothing needs. Only the `G α` shape turns a missing witness into an
error, and it does so because there is no term to emit. CI therefore runs:

```sh
lake clean palamedes && lake build --wfail      # `clean palamedes` keeps Mathlib cached
```

Do the same before claiming a change is green, or grep build output for warnings.

Debugging:

```lean
set_option trace.Palamedes.derive true   -- print every command `derive_palamedes` generates
set_option trace.palamedes.trace true    -- synthesis pipeline timing/trace nodes
set_option palamedes.debug true          -- pipeline debug messages
```

`scripts/profile.py` benchmarks synthesis over the corpus by parsing `palamedes.trace` nodes; it has
two hardcoded file lists (`STANDARD` = structurally-recursive spelling, `FOLD` = catamorphism
spelling), a `FILES = …` line to switch between them, and an `EXCLUDED` list for the corpus files it
deliberately skips. It fails loudly if a listed path rotted or a corpus file is listed nowhere, and
its `PARTIAL_RETURN_TYPE` regex classifies benchmarks by *declared return type* — keep it in sync if the
partiality convention changes.

## Architecture

### The five-stage pipeline

`generator_search` ([Synthesizer/FrontEnd.lean](Palamedes/Synthesizer/FrontEnd.lean),
`runSynthesisPipeline` — shared with `@[correct]`):

1. **Search** — `cgenerator_search` ([Synthesizer/CGeneratorSearch.lean](Palamedes/Synthesizer/CGeneratorSearch.lean))
   runs Aesop over the `synthesis` rule set looking for an inhabitant of
   `CorrectGen P := {g : PGen α // g.support = P}` ([CorrectGen.lean](Palamedes/CorrectGen.lean)).
   Synthesis is literally proof search for a correct-by-construction generator.
2. **Extract** — the `extract` simp set ([Extract.lean](Palamedes/Extract.lean)) pulls the raw `PGen`
   out of the `CorrectGen` term: one `.val` equation per synthesis combinator. Unfolding exactly the
   combinator wrappers (rather than delta-reducing) is why the combinators need not be `@[reducible]`.
3. **Optimize** — [Optimizer.lean](Palamedes/Optimizer.lean) on top of the
   [GenTransform.lean](Palamedes/GenTransform.lean) substrate. **Proof-carrying**: every rewrite
   composes a `support`-preservation proof that is type-checked before the goal closes; each rewrite's
   twin lemma lives in [Support.lean](Palamedes/Support.lean). Two passes — monad laws +
   assume-floating, then collapsing `pick` trees into uniform `oneOf`s.
4. **Totality** — [Synthesizer/Totality.lean](Palamedes/Synthesizer/Totality.lean) reconstructs a
   `TGen` witness. This is a **structural descent, not a search**: rules are keyed by the head
   constant they reconstruct, so order can't matter and a tagged-but-unreachable rule is impossible.
5. **Package** — at the declared shape, of which there are exactly two and both are Basalt's: `G α`
   projected from the `TGen` witness by `extractWitness`, or `G (Option α)` read at `OptionT G` by
   `extractPartialWitness` — the carrier's `.run` instantiated there and pushed inward until only
   Basalt vocabulary is left, so a rejecting `assume` becomes an ordinary `pure none` draw.
   `Palamedes.PGen` is internal to stages 2–4, is not declarable (`classifyGoal` rejects a goal
   typed at it like any other non-`Gen` type), and does not appear in an emitted term at either
   shape. `PalamedesTest/Extract.lean`'s `isCarrierResidue` is what enforces the second half.

   The push needs no `Option`-flavoured recursion scheme: `X.run_unfold` is stated at an arbitrary
   `G` with `Fail G`, so it fires at `OptionT G`, and `X.unfoldGo`'s own `G`-polymorphism is what
   makes the recursion short-circuit on `none`. What it does need is the three things `.run` does
   not distribute over on its own — `dite`, `ite`, and a `match`. The first two get
   `PGen.run_dite`/`run_ite`; the third gets `pushRunMatch?`, which rebuilds the matcher at the
   run-type motive and proves the step by instantiating that same matcher at a `Prop` motive where
   every arm is `rfl`. All three are *propositional*, not definitional, which is why stage 5 hands
   `@[correct]` an `emitted = PGen.totalize gen` equation (`SynthesisStash.partialEq?`) rather than
   relying on `isDefEq`.

### Core types

- `PGen α` ([PGen.lean](Palamedes/PGen.lean)) — a *structure* wrapping `∀ {G} [Gen G] [Fail G], G α`.
  `support g := SPMF.support g.run`. Failure is an explicit capability rather than Basalt's CCPO
  bottom; the `Fail` class docstring says why.
- `TGen α` ([Total.lean](Palamedes/Total.lean)) — the same, *without* `Fail`. So "never filters" is
  the structural fact "typeable without `Fail`" — that is `PGen.total`, which is `Type`-valued: the
  witness *is* the failure-free generator the Basalt shape gets projected from.
- **Totality ≠ termination**, and the two are orthogonal — `PGen.total`'s docstring says why, and
  [Sample.lean](Palamedes/Sample.lean)'s says what that costs a sampler.

### Every generator is declared at a Basalt shape

Every generator in `PalamedesTest/Corpus/` is `[Gen G] : G τ` (or `G (Option τ)` when it filters),
and so is every generator anyone can write: `Palamedes.PGen` is not a declarable goal.

That is load-bearing rather than cosmetic. Packaging at the carrier would return the optimized
generator directly and **never project the totality witness**, so every defect in witness
*construction* is invisible from a carrier-shaped declaration. Do not reintroduce a shape that
skips stage 4's projection.

So: when adding a `@[total]` rule, the discipline in `Total.lean`'s docstring is not stylistic.
Direct `⟨data, proof⟩`, tactics confined to the proof, and any case split (`match`, `dite`, `ite`,
recursor) **inside** `TGen.mk` so `.run` cancels at the top.

That last move is available exactly when the combinator's branches are **non-dependent**, so keep
them that way. A branch that receives the equation its own arm establishes makes the branch's *type*
mention the scrutinee, so the witness's `match` generalizes it too and `.val` has nothing to project
— the only escape is a hand-written failure-free `TGen` twin of the combinator, per datatype, that
no registry validates. `PGen.caseTy` is the worked example: dropping two proof arguments its only
caller discarded anyway is what lets `total_Ty_caseTy` use the same `TGen.mk` split as
`X.total_cases`.

`PalamedesTest/Extract.lean` is the backstop, and it distinguishes a `TGen`-valued *primitive* under
`.run` (legitimate: the only way to spell a failure-free primitive at `G`) from the witness
machinery (residue). Keep that distinction if you touch `isResidue`; the combinator basis it checks
against is `Palamedes.tgenBasis`, the same list `extractWitness` unfolds.

### An assume-free primitive is spelled at `TGen`, and `PGen` gets the coercion

Which of a combinator's two spellings has to exist, and why generator-valued arguments are the whole
criterion, is [Total.lean](Palamedes/Total.lean)'s combinators section header. The worked examples it
routes to: `PGen.choose` for a primitive coerced from the core algebra, `Data/Nat.lean`'s `gt`/`lt`
for composites that need no `TGen` spelling at all, and `Data/List/Elements.lean`'s `elements` for
what a recursive primitive costs if spelled the other way round.

The choice is visible in the emitted terms, which name their sub-generators: `genGoodStack`'s
label draws print as `TGen.arbLabel.run`, and `genWellScoped`'s type draws as `TGen.arbTy.run`.
A primitive left at `PGen` gets inlined at every use site instead.

### Partiality is a fact about the declared type

A generator whose synthesis leaves a rejecting `PGen.assume` must be declared at `G (Option α)`;
declaring it at `G α` is an error that names the fix. Do not reintroduce a flag for this.

For a `G (Option β)` goal, `classifyGoal` ([FrontEnd.lean](Palamedes/Synthesizer/FrontEnd.lean))
tries the **filtering** reading (`β → Prop`) first and the total-of-options reading second. That
order must not be flipped; why (a silent `Option` coercion) is the comment on its `Option` branch,
and `PalamedesTest/GeneratorAPI.lean`'s "the predicate, not the goal, picks the reading" section
pins the behavior.

### Tag-driven registries: "adding a datatype is one line"

`derive_palamedes X` ([Derive/](Palamedes/Derive/)) generates the whole
per-datatype layer — base functor, `fold`, `accuM`, the `unfold` recursion scheme, support/totality
lemmas, fold/`accuM` fusion lemmas — and registers it. **No edit to any `Palamedes/` module is
needed.** [PalamedesTest/Corpus/LeafTree/](PalamedesTest/Corpus/LeafTree/) proves this end to end by
declaring a brand-new datatype inside a test file. A finite enumeration has no recursion scheme to
generate; `derive_enum_gen X` ([Derive/Enum.lean](Palamedes/Derive/Enum.lean)) covers its draw layer
instead. Neither generates a case-split rule — that shape is per-datatype and the corpus is its
oracle; `Data/Bool.lean`'s `s_caseBool` documents the one measured case.

That works because every pipeline stage reads a registry rather than a hardcoded list. When adding a
capability, **tag it; don't add it to a list inside the synthesizer**:

| Registry | Stage it feeds |
| --- | --- |
| `synthesis` Aesop rule set ([RuleSets.lean](Palamedes/RuleSets.lean)) | search |
| `unfold_strategy` ext ([UnfoldStrategy.lean](Palamedes/UnfoldStrategy.lean)), amended by `unfold_strategy_cond` / `unfold_strategy_convert` | unfold synthesis |
| `@[case_split]` ([CaseSplit.lean](Palamedes/CaseSplit.lean)), keyed by the scrutinee's type | case-split rule |
| `@[extract]`, `@[totality_witness]`, `@[partial_witness]` simp sets ([Extract.lean](Palamedes/Extract.lean)) | extraction, and the two packagings |
| `@[gen_congr]` ([OptimizeCongr.lean](Palamedes/OptimizeCongr.lean)) | optimizer descent |
| `@[total]` ([RuleSets.lean](Palamedes/RuleSets.lean)), keyed by head constant | totality reconstruction |

Attributes parse and validate their lemma's shape *at tag time* (`analyzeCongr`, `totalKey?`,
one-rule-per-head), so a malformed or duplicate registration is rejected loudly rather than silently
dropped later. Preserve that property.

Rejected by design, loudly: mutual, nested, and indexed inductives; non-`Type` parameters; dependent
constructor fields. A rose tree (`node : List (Tree α) → Tree α`) is the canonical unsupported shape.

### Commands layered on the pipeline

- `@[correct]` ([Synthesizer/Correct.lean](Palamedes/Synthesizer/Correct.lean)) — the tactic stashes
  its proofs in `synthesisExt` (`FrontEnd.lean`); the attribute, at
  `applicationTime := .afterCompilation`, `addDecl`s them as named theorems. The names follow
  Basalt's `#genstats` law-naming contract (`<gen>.sound_complete` &c., found by name and
  statement-checked — basalt's `GenStats/Command.lean` owns the list), so the reports pick them up
  with no registry. It reports what it emitted. **Two constraints on what crosses that
  boundary**, both silent failures otherwise: the stash must be closed over
  `declBinders` (the tactic-site local context also holds the recursive self-reference, flagged
  `isAuxDecl`), and it must be metavariable-free *including levels* — the attribute runs in a fresh
  `MetaM`, where a survivor surfaces as `unknown universe metavariable` against the `def` with no
  `?m` visible in it. This is not a command: `Term.getDeclName?` gives a tactic the declaration name,
  so only *ordering* ever required one, and Lean keeps binder elaboration and auto-bound implicits.
- `installTuning` ([Tuning.lean](Palamedes/Tuning.lean)) — **a pipeline stage, not a command**,
  run between optimize and totality: a `Tuning` binder in the declaration's signature is threaded
  through every choice site, and running before packaging is why one generator, one witness, and
  one θ-generalized `sound_complete` suffice. `PalamedesTest/Tuning.lean`'s header owns the design
  and pins it.
- `SchedulePolicy` ([Schedule.lean](Palamedes/Schedule.lean)) — depth-indexed affine weight
  schedules, pure `Tuning`-producing data with no dependency on the optimizer. Decay is base-weight
  *growth*, never recursive-weight shrinkage: a weight of `0` would drop a branch from the support,
  so every weight stays `≥ 1`. This is what makes recursive generators terminate in practice.
- [Laws.lean](Palamedes/Laws.lean) / [SomeSupport.lean](Palamedes/SomeSupport.lean) — bridges from
  Palamedes `support` facts to the emitted laws: Basalt's `IsSoundAndComplete`, and — for the
  filtering path — `IsSomeSoundAndComplete`, which is Palamedes' own (defined in `Laws.lean`;
  Basalt has no filtering law) over `OptionT SPMF`.

### Import ordering matters

Why [Palamedes/Data.lean](Palamedes/Data.lean) aggregates every datatype module — and why corpus
files deliberately import *individual* modules instead — is that file's own docstring. Don't "tidy"
corpus imports into the aggregator.

### A corpus file opens `Palamedes` and nothing else

Not `Palamedes.PGen`, and not `Palamedes.PGen.CorrectGen`. A corpus file's job is to *read* emitted
terms, and an emitted term is packaged at the Basalt shapes, so its choice sites are **Basalt's**
root-level `frequency` — while `Palamedes.PGen` carries a combinator of the same name. Open the
carrier and it shadows Basalt's, `unresolveNameGlobal` has no short spelling left, and every
generator in the file prints its choice sites as `_root_.frequency`.

What survives the narrower `open` is what should: Basalt's `frequency` and `chooseNat` print bare,
and a *filtering* generator's `OptionT`-level operations print as `OptionT.pure`/`OptionT.bind` —
qualified, which is honest about the monad the term is read at. Everything still re-elaborates when
pasted, which is the pins' actual contract, and it is why those are left alone rather than folded
back into `pure`/`do`: a branch's expected type is at `G`, not `OptionT G`, so the notation would
not elaborate there.

The same clash is one `namespace` line away whenever a `Data/` module adds a failure-free primitive,
which is why each puts them in an explicit `namespace TGen … end TGen` block ahead of the
`namespace PGen` one that coerces them. `Data/Nat.lean`'s primitive section header owns that fact.

## Gotchas whose failure mode is silence

- **Unrelated-looking `#guard_msgs` diffs plus totality warnings, all at once**, with extraction
  leaving `Subtype.val` behind: `CorrectGen` lost its `@[implicit_reducible]`, so every `extract`
  rewrite silently stopped firing and the optimizer no-opped on an unrecognized head.
  [CorrectGen.lean](Palamedes/CorrectGen.lean) documents the transparency mismatch. Diagnose with
  `set_option trace.Meta.Tactic.simp.unify true`; a "failed to unify" whose two sides differ only by
  `CorrectGen` vs `Subtype` is this.

- **An emitted generator that reads as a proof term** — a tree of `total_*` applications, a
  `._proof_i` wall, a splitter and an `Eq.rec` per arm — is a break in one of four independent
  mechanisms, each fenced where it lives: the direct `⟨data, proof⟩` discipline
  ([Total.lean](Palamedes/Total.lean)), `extractWitness`'s deliberately partial reduction
  ([FrontEnd.lean](Palamedes/Synthesizer/FrontEnd.lean)), `X.total_cases`
  ([Synthesizer/Totality.lean](Palamedes/Synthesizer/Totality.lean)), and `delabDroppingProof`'s
  registrations ([PGen.lean](Palamedes/PGen.lean)). The break is misattributed because the symptom is
  a pinned *term*, three stages downstream of whichever one gave way.

- **Aesop reports "made no progress" on a predicate the corpus synthesizes fine.** Two causes, both
  silent. An unqualified identifier in a `(by …)` rule script: those resolve at search time in the
  *caller's* scope, so a rule fires only where the caller happens to `open` the right namespace —
  hence the `_root_`-rooted rules in
  [CGeneratorSearch.lean](Palamedes/Synthesizer/CGeneratorSearch.lean), and keep new ones that way.
  Or a tag in a module that does not *import* [RuleSets.lean](Palamedes/RuleSets.lean): an Aesop rule
  set is not visible in the module declaring it. Same failure mode as the `Data.lean` import-ordering
  note above.

- **A `PGen`-valued argument with no `@[gen_congr]` lemma fails the traversal loudly** rather than
  being skipped — preserve that. `oneOf`/`frequency` are the two exceptions, exempt *by name*, each
  with a bespoke descent in [GenTransform.lean](Palamedes/GenTransform.lean) that documents why.

## Test layout

- `PalamedesTest/Corpus/` — the synthesis corpus. `Simple/` and `Range/` are the easiest entry
  points. Each datatype directory generally carries two spellings of the same predicate: a
  structurally recursive one (e.g. `BST.lean`) and an explicit catamorphism (`Fold.lean`). These are
  **not duplicates** — they exercise different paths through the search.
- `PalamedesTest/Foo.lean` guards `Palamedes/Foo.lean`, so the two directory listings diff into a
  coverage map. Notable guards: `Extract.lean` fails the build if synthesis residue (`Subtype.val`,
  `Eq.mpr`, `CorrectGen`, a totality-witness constructor, a bare `PGen.pick`) survives into a
  compiled term's data path; `Derive.lean` pins generated signatures and `#print axioms`;
  `Schedule.lean` pins `#genstats` distribution reports under `#guard_msgs`. Three files have no
  library counterpart and are named for what they pin instead: `GeneratorAPI.lean` (the
  shape/totality dispatch table, and every message `classifyGoal` can produce), `TotalWitness.lean`
  (stages 1–4 run one tactic at a time, so a defect in the witness mechanics is localized rather
  than surfacing as a wrong emitted term), and `Stats.lean` (distribution oracles: pinned
  `#genstats` reports, including for the generators too large to term-pin). `Harness.lean` guards
  nothing; it holds the walk-with-backstop and companion assertions the audit modules share.

## Documentation rules

1. One owner per fact. Every fact lives in exactly one place; other mentions are a pointer. The
   owner is the file whose edit would falsify the fact — a number, name, or list set in code is
   documented where it is set, never quoted elsewhere.
2. CLAUDE.md is a map, not a mirror: workflow, architecture no single file owns, routing to worked
   examples, and these rules. No fact a code edit can falsify.
3. The default is no comment. The compiler, a test, or a pin is the fence wherever it can be — a
   mistake that fails loudly and locally needs no warning, however tempting the edit.
4. A warning comment must be backed by a failure that actually happened (or a symptom that cannot
   be traced locally) AND that was silent, delayed, or misattributed. Hypothetical mistakes get no
   fence.
5. A fence is two sentences: the forbidden edit, the observed symptom. Only a misattributed
   failure also earns an entry in CLAUDE.md's gotcha section (symptom → cause → pointer), because
   its victim is looking at the wrong file.
6. No process narration ("the probe", "previously we") — git history holds the story; comments
   hold the contract.
7. When a hazard can be made a build failure, build the check and delete the prose. A fence
   comment is the fallback, not the goal.
8. Module docstrings are 1–3 sentences: what the module is, the invariant it protects. Hazard
   prose lives on the declaration that carries the hazard.
9. An edit that fans out into many mechanical fixes is a design signal: stop and reconsider the
   approach; do not qualify or patch through the errors.
10. Background theory is cited, not taught. A fact about Lean, Mathlib, or type theory is owned
    upstream: state its local consequence (the lemma that cannot exist, the tactic that cannot be
    used here) and name the concept so a reader can find the real treatment ("a free theorem";
    "tactic-mode `cases` elaborates to the recursor"). Explain a mechanism only when it has no
    citable name — version-specific or undocumented behavior — and then as a rule-4 fence.

## Conventions

- Every module opens with the MIT copyright header and a `/-! # … -/` module docstring, sized and
  scoped per the documentation rules above.
- Declaration docstrings explain design tension, not just signature — where rule 4 admits one.
- Lean toolchain is pinned in `lean-toolchain`; deps in `lakefile.toml` / `lake-manifest.json`.
  Mathlib/Aesop/Plausible and Basalt are all pinned to release tags.
