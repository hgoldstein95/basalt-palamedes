import PalamedesTest.Corpus
import PalamedesTest.GeneratorAPI

/-!
# Extraction audit

Every example in `PalamedesTest/Examples/` synthesizes a generator at elaboration time, but a
silent extraction failure does not break the build: if the `extract` simp set fails to
strip the `CorrectGen` combinator wrappers, the generator is left unchanged, so the optimizer's
support-preservation proof still holds trivially, and a `totality` failure is only a warning. The
result is a definition that elaborates fine but contains `(… : CorrectGen P).val` wrappers instead
of raw `Gen` code.

This module walks every generator-typed definition in the example corpus and *fails to compile* if
any synthesis residue survives in a compiled term.

**It must recognise both generator shapes.** It originally matched only a `Palamedes.Gen α` head, so
when emission moved to the Basalt shape (`{G} → [Gen G] → G α`, whose head under the telescope is a
*local* `G` rather than a constant) every such generator was silently skipped — and the `total == 0`
backstop stayed quiet because the corpus still contained Palamedes-shaped ones. The audit narrowed
to a shrinking subset at exactly the moment the representation changed. A check that cannot fail is
never checked; that is the same failure this module exists to prevent, one level up.
-/

open Lean Meta Elab Command

namespace PalamedesTest.ExtractionAudit

/-- Constants that should never survive extraction into a synthesized generator: the
`CorrectGen` combinators themselves, the `Subtype.val` projection that extraction is supposed
to eliminate, and `Eq` casts (which would mean a rewrite leaked out of a `convert` proof
argument into the generator). Matcher auxiliaries (e.g. `Gen.CorrectGen.List.s_unfold.match_1`)
are exempt: they are ordinary case splits that legitimately appear in `s_unfold` generators.
Proof auxiliaries (`…._proof_i`, abstracted out of combinator bodies by the definition
elaborator) are exempt too: they are compiler-erased proofs of `Prop`s, never a combinator
wrapper (those are `Type`-valued).

`Gen.pick` is residue too, of the optimizer rather than of extraction: the flatten pass rewrites
every `pick` tree into a uniform n-ary `oneOf`, so a `pick` surviving in a compiled
synthesized generator means a chain escaped flattening — and with it the `½, ¼, ⅛, …` distribution
skew the pass exists to remove. -/
def isResidue (c : Name) : Bool :=
  if (c.toString.splitOn ".match_").length > 1 then false
  else if (c.toString.splitOn "._proof_").length > 1 then false
  else
    c == ``Subtype.val || c == ``Eq.mpr || c == ``Eq.rec || c == ``Palamedes.CorrectGen ||
    c == ``Palamedes.Gen.pick ||
    (`Palamedes.Gen.CorrectGen).isPrefixOf c ||
    -- Totality residue. A Basalt-shaped generator is emitted from the `TGen` witness, so if the
    -- witness's `.val`/`.run` did not reduce away, what lands in the environment is the *proof* and
    -- not the generator — readable as a witness tree rather than as generator code. `Eq.rec` above
    -- already catches the `▸` such a tree carries; these name the cause rather than the symptom.
    (`Palamedes.Gen.Total).isPrefixOf c || (`Palamedes.TGen).isPrefixOf c ||
    c == ``Palamedes.Gen.total || c.toString.endsWith "total_unfold"

run_cmd liftTermElabM do
  let env ← getEnv
  let mut total := 0
  for i in [0:env.header.moduleData.size] do
    let modName := env.header.moduleNames[i]!
    -- `GeneratorAPI` alongside the corpus: it holds the canonical Basalt-shaped generators, which
    -- is the default emission shape and therefore the one most in need of auditing.
    unless (`PalamedesTest.Corpus).isPrefixOf modName
        || modName == `PalamedesTest.GeneratorAPI do continue
    for n in env.header.moduleData[i]!.constNames do
      let some ci := env.find? n | continue
      let some val := ci.value? | continue
      let isGen ← forallTelescope ci.type fun args body => do
        -- The synthesis-internal carrier...
        if body.getAppFn.constName? == some ``Palamedes.Gen then return true
        -- ...or Basalt-shaped, `G α` for a `G` bound by this very telescope.
        let hd := body.getAppFn
        return hd.isFVar && args.any (· == hd)
      unless isGen do continue
      total := total + 1
      let bad := val.getUsedConstants.filter isResidue
      unless bad.isEmpty do
        logError m!"extraction left synthesis residue in {n}: {bad.toList}"
  if total == 0 then
    logError "extraction audit found no generators to check; is the example corpus imported?"

end PalamedesTest.ExtractionAudit
