/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import PalamedesTest.Corpus
import PalamedesTest.GeneratorAPI

/-!
# Extraction audit

Every example in `PalamedesTest/Corpus/` synthesizes a generator at elaboration time, but a
silent extraction failure does not break the build: if the `extract` simp set fails to
strip the `CorrectGen` combinator wrappers, the generator is left unchanged, so the optimizer's
support-preservation proof still holds trivially, and a `totality` failure is only a warning. The
result is a definition that elaborates fine but contains `(… : CorrectGen P).val` wrappers instead
of raw `PGen` code.

This module walks every generator-typed definition in the example corpus and *fails to compile* if
any synthesis residue survives in a compiled term.

**It must recognise every generator type it might meet** — the Basalt `{G} → [Gen G] → G α` that
`generator_search` emits, whose head under the telescope is a *local* `G` rather than a constant,
plus the two types a synthesized generator is assembled out of and can therefore be written at by
hand: `Palamedes.PGen α` and `CorrectGen P`. A shape the walk fails to match is silently unaudited,
and the `total == 0` backstop does not catch it so long as some other shape still matches.
-/

open Lean Meta Elab Command

namespace PalamedesTest.ExtractionAudit

/-- Constants that should never survive extraction into a synthesized generator: the
`CorrectGen` combinators themselves, the `Subtype.val` projection that extraction is supposed
to eliminate, and `Eq` casts (which would mean a rewrite leaked out of a `convert` proof
argument into the generator). Matcher auxiliaries (e.g. `PGen.CorrectGen.List.s_unfold.match_1`)
are exempt: they are ordinary case splits that legitimately appear in `s_unfold` generators.
Proof auxiliaries (`…._proof_i`, abstracted out of combinator bodies by the definition
elaborator) are exempt too: they are compiler-erased proofs of `Prop`s, never a combinator
wrapper (those are `Type`-valued).

`PGen.pick` is residue too, of the optimizer rather than of extraction: the flatten pass rewrites
every `pick` tree into a uniform n-ary `oneOf`, so a `pick` surviving in a compiled
synthesized generator means a chain escaped flattening — and with it the `½, ¼, ⅛, …` distribution
skew the pass exists to remove. -/
def isResidue (c : Name) : Bool :=
  if (c.toString.splitOn ".match_").length > 1 then false
  else if (c.toString.splitOn "._proof_").length > 1 then false
  else
    c == ``Subtype.val || c == ``Eq.mpr || c == ``Eq.rec || c == ``Palamedes.CorrectGen ||
    c == ``Palamedes.PGen.pick ||
    (`Palamedes.PGen.CorrectGen).isPrefixOf c ||
    -- Totality residue. A Basalt-shaped generator is emitted from the `TGen` witness, so if the
    -- witness's `.val`/`.run` did not reduce away, what lands in the environment is the *proof* and
    -- not the generator — readable as a witness tree rather than as generator code. `Eq.rec` above
    -- already catches the `▸` such a tree carries; these name the cause rather than the symptom.
    --
    -- `TGen` is deliberately **not** blanket-flagged. A `TGen`-valued *primitive* applied to `.run`
    -- — `TGen.arbNat.run`, `(TGen.choose lo hi).run` — is not residue but the only way to spell a
    -- failure-free primitive at `G`: its `PGen` form is that same generator coerced, and cannot
    -- appear in a term typed without `Fail`. What *is* residue is the witness machinery: the
    -- `total_*` lemmas, `PGen.total` itself, and the `TGen` combinator basis `extractWitness` is
    -- supposed to have unfolded (a survivor there means extraction stopped early). `Subtype.val`
    -- above catches the rest. The basis is read from `Palamedes.tgenBasis`, the same list
    -- `extractWitness` unfolds, so the two cannot drift.
    (`Palamedes.PGen.Total).isPrefixOf c ||
    Palamedes.tgenBasis.contains c ||
    c == ``Palamedes.PGen.total || c.toString.endsWith "total_unfold"

run_cmd liftTermElabM do
  let env ← getEnv
  let mut total := 0
  for i in [0:env.header.moduleData.size] do
    let modName := env.header.moduleNames[i]!
    -- `GeneratorAPI` alongside the corpus: it holds the canonical Basalt-shaped generators, which
    -- is the emission shape and therefore the one most in need of auditing.
    --
    -- `Correct` and `Tuning` are listed for the same reason and **do not currently reach this
    -- loop**: a module is only walkable if it is in this file's import closure, and those two
    -- cannot be imported here because they declare root-level names (`isAllTwos`, `genAllTwos`,
    -- `genBetween`) that collide with `GeneratorAPI`'s. Closing that hole means namespacing each
    -- test module's helpers, which moves every `#guard_msgs` pin in them. What goes unaudited
    -- meanwhile is `@[correct]`'s raw `addDecl` path — no def elaborator, so none of the
    -- `._proof_i` abstraction the exemption above assumes. (The *generator* is an ordinary `def`,
    -- since synthesis is a tactic throughout; it is the emitted law that takes the raw path.)
    unless (`PalamedesTest.Corpus).isPrefixOf modName
        || modName == `PalamedesTest.GeneratorAPI
        || modName == `PalamedesTest.Correct
        || modName == `PalamedesTest.Tuning do continue
    for n in env.header.moduleData[i]!.constNames do
      let some ci := env.find? n | continue
      let some val := ci.value? | continue
      let isGen ← forallTelescope ci.type fun args body => do
        -- The synthesis-internal carrier...
        if body.getAppFn.constName? == some ``Palamedes.PGen then return true
        -- ...or bundled: a `CorrectGen`-typed def's *data* component is a generator, and skipping
        -- the bundle entirely is how this audit would go quiet at the next representation change.
        -- Only when no *argument* is `CorrectGen`-typed: a def consuming `CorrectGen`s is a
        -- combinator (`s_unfold` &c.), whose business is exactly the `.val` projections and
        -- `CorrectGen` mentions this audit calls residue in a synthesized generator.
        if body.getAppFn.constName? == some ``Palamedes.CorrectGen then
          return !(← args.anyM fun a => do
            return (← inferType a).getUsedConstants.contains ``Palamedes.CorrectGen)
        -- ...or Basalt-shaped, `G α` for a `G` bound by this very telescope.
        let hd := body.getAppFn
        return hd.isFVar && args.any (· == hd)
      unless isGen do continue
      total := total + 1
      -- Scan the **data** path only. Proof subterms are compiler-erased and legitimately sit in
      -- argument positions of a generator (`frequency`'s positivity side condition, `choose`'s
      -- bounds); flagging those would make every raw-`addDecl` emission a
      -- false positive. The def elaborator hides them behind exempt `._proof_i` names; raw
      -- `addDecl` keeps them inline, so the erasure has to be structural rather than name-based.
      let cleaned ← Meta.transform val (pre := fun e => do
        if !e.isApp && !e.isLambda && !e.isForall && !e.isLet then return .continue
        if ← Meta.isProof e then return .done (mkConst ``True.intro) else return .continue)
      let bad := cleaned.getUsedConstants.filter isResidue
      unless bad.isEmpty do
        logError m!"extraction left synthesis residue in {n}: {bad.toList}"
  if total == 0 then
    logError "extraction audit found no generators to check; is the example corpus imported?"

end PalamedesTest.ExtractionAudit
