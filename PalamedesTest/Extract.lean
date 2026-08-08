/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import PalamedesTest.Corpus
import PalamedesTest.GeneratorAPI
import PalamedesTest.Harness
import PalamedesTest.Synthesizer.Correct
import PalamedesTest.Tuning

/-!
# Extraction audit

Every example in `PalamedesTest/Corpus/` synthesizes a generator at elaboration time, but a
silent extraction failure does not break the build: if the `extract` simp set fails to
strip the `CorrectGen` combinator wrappers, the generator is left unchanged, so the optimizer's
support-preservation proof still holds trivially, and a `totality` failure is only a warning. The
result is a definition that elaborates fine but contains `(… : CorrectGen P).val` wrappers instead
of raw `PGen` code.

This module walks every generator-typed definition in the example corpus and in the `@[correct]`
fixtures, and *fails to compile* if any synthesis residue survives in a compiled term.

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
argument into the generator). Compiler-generated auxiliaries are exempt wholesale, since none of
them can be a combinator wrapper: matchers (`PGen.CorrectGen.List.s_unfold.match_1`) are ordinary
case splits that legitimately appear in `s_unfold` generators, and the proof auxiliaries the
definition elaborator abstracts out of combinator bodies (`…._proof_i`) are erased proofs of
`Prop`s, while a wrapper is `Type`-valued.

`PGen.pick` is residue too, of the optimizer rather than of extraction: the flatten pass rewrites
every `pick` tree into a uniform n-ary `oneOf`, so a `pick` surviving in a compiled
synthesized generator means a chain escaped flattening — and with it the `½, ¼, ⅛, …` distribution
skew the pass exists to remove. -/
def isResidue (c : Name) : Bool :=
  if c.isInternalDetail then false
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
    -- — `TGen.arbNat.run`, `TGen.elements.run` — is not residue but the only way to spell a
    -- failure-free primitive at `G`: its `PGen` form is that same generator coerced, and cannot
    -- appear in a term typed without `Fail`. `TGen.choose` is not one of these: it is a view of
    -- Basalt's `chooseNat` and sits in the basis below, so a survivor of it *is* residue.
    -- What *is* residue is the witness machinery: the
    -- `total_*` lemmas, `PGen.total` itself, and the `TGen` combinator basis `extractWitness` is
    -- supposed to have unfolded (a survivor there means extraction stopped early). `Subtype.val`
    -- above catches the rest. The basis is read from `Palamedes.tgenBasis`, the same list
    -- `extractWitness` unfolds, so the two cannot drift.
    (`Palamedes.PGen.Total).isPrefixOf c ||
    Palamedes.tgenBasis.contains c ||
    c == ``Palamedes.PGen.total || c.toString.endsWith "total_unfold"

/-- Residue of the **filtering** path, which only a Basalt-shaped term can carry.

A generator declared `G (Option _)` is the optimized `PGen` read at `OptionT G` with the projection
pushed inward, so a carrier combinator surviving means the push stopped early — most often at a case
split it could not distribute through, which leaves the branches underneath as bare `PGen.mk`s.

Kept separate from `isResidue` because the same constants are perfectly good in a term that is
*declared* at the carrier: `derive_palamedes` emits a `PGen`-valued recursion scheme built from
`PGen.mk`, and `GeneratorAPI`'s rendering fixtures are hand-written `PGen.oneOf`s. Neither went
through the pipeline. -/
def isCarrierResidue (c : Name) : Bool :=
  Palamedes.pgenBasis.contains c ||
  c == ``Palamedes.PGen.mk || c == ``Palamedes.PGen.run || c == ``Palamedes.PGen.totalize

-- Alongside the corpus: `GeneratorAPI` holds the canonical Basalt-shaped generators, and
-- `Synthesizer.Correct` and `Tuning` are what put `@[correct]`'s emission path under the walk.
--
-- Only modules in *this file's import closure* are walkable at all, so each has to be imported
-- above as well as accepted here. `TotalWitness` is deliberately absent: it spells the pipeline out
-- one tactic at a time, so its `genAllTwosBasalt` *is* an unreduced `witness.val.run` — residue
-- everywhere else, and the point of the file there.
run_cmd
  liftTermElabM <| auditConstants
      (fun m => (`PalamedesTest.Corpus).isPrefixOf m || m == `PalamedesTest.GeneratorAPI ||
        m == `PalamedesTest.Synthesizer.Correct || m == `PalamedesTest.Tuning)
      "extraction audit found no generators to check; is the example corpus imported?"
      fun n => do
      let some ci := (← getEnv).find? n | return false
      let some val := ci.value? | return false
      -- `none` for a non-generator; otherwise whether the shape is Basalt's, which is what decides
      -- if the carrier constants count as residue.
      let basaltShaped? ← forallTelescope ci.type fun args body => do
        -- The synthesis-internal carrier...
        if body.getAppFn.constName? == some ``Palamedes.PGen then return some false
        -- ...or bundled: a `CorrectGen`-typed def's *data* component is a generator, and skipping
        -- the bundle entirely is how this audit would go quiet at the next representation change.
        -- Only when no *argument* is `CorrectGen`-typed: a def consuming `CorrectGen`s is a
        -- combinator (`s_unfold` &c.), whose business is exactly the `.val` projections and
        -- `CorrectGen` mentions this audit calls residue in a synthesized generator.
        if body.getAppFn.constName? == some ``Palamedes.CorrectGen then
          if ← args.anyM (fun a => do
              return (← inferType a).getUsedConstants.contains ``Palamedes.CorrectGen) then
            return none
          return some false
        -- ...or Basalt-shaped, `G α` for a `G` bound by this very telescope.
        let hd := body.getAppFn
        if hd.isFVar && args.any (· == hd) then return some true else return none
      let some isBasalt := basaltShaped? | return false
      -- Scan the **data** path only. Proof subterms are compiler-erased and legitimately sit in
      -- argument positions of a generator (`frequency`'s positivity side condition, `choose`'s
      -- bounds); flagging those would make every raw-`addDecl` emission a
      -- false positive. The def elaborator hides them behind exempt `._proof_i` names; raw
      -- `addDecl` keeps them inline, so the erasure has to be structural rather than name-based.
      let cleaned ← Meta.transform val (pre := fun e => do
        if !e.isApp && !e.isLambda && !e.isForall && !e.isLet then return .continue
        if ← Meta.isProof e then return .done (mkConst ``True.intro) else return .continue)
      let bad := cleaned.getUsedConstants.filter
        (fun c => isResidue c || (isBasalt && isCarrierResidue c))
      unless bad.isEmpty do
        logError m!"extraction left synthesis residue in {n}: {bad.toList}"
      return true

end PalamedesTest.ExtractionAudit
