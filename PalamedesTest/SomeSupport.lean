/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes
import PalamedesTest.Harness

/-!
# `someSupport` twin inventory

Every hand-written primitive pays a standing tax: its `support_X` characterization needs a
`someSupport_X` twin, or the first *filtering* `@[correct]` whose generator uses the primitive fails
at the law bridge (`Synthesizer/Correct.lean` discharges `someSupport g = P` by simp over the twins).
The tax is per-primitive and easy to forget precisely because nothing consumes the twin until a
filtering generator happens to reach it — the gap is silent until someone else's `@[correct]`
breaks.

This module makes the gap loud instead: it walks every `support_*` lemma in `Palamedes/Data/` and
*fails to compile* if the `someSupport_*` twin next to it is missing, or if the twin does not
actually characterize `someSupport` — a conventionally-named lemma stating something else would
otherwise satisfy a name-only check while leaving the bridge just as broken.

Exempt: `*_congr` lemmas and case-split combinators (`support_Ty_caseTy` &c.), which state
*relative* facts rather than characterizations, so there is no `someSupport` reading to demand.

Case-split twins are deliberately **not** demanded, and `genRBT` is the proof that they need not be:
it is a filtering generator that cases on a derived base functor, and it carries a law. The bridge
gets past the `match` by case-splitting it rather than by rewriting through it, which is also the
only thing that *could* work — a `someSupport_cases` simp lemma never fires, because matchers are
per-elaboration and simp matches at `reducible`. See `Synthesizer/Correct.lean`'s `.basaltOption`
branch.
-/

open Lean Meta Elab Command

namespace PalamedesTest.SomeSupport

/-- The case-split combinators, which state a *relative* fact about their arms rather than
characterizing a support. Naming them one by one is what makes each addition a decision. -/
def exemptCaseSplits : Array Name := #[``Palamedes.PGen.support_Ty_caseTy]

run_cmd
  liftTermElabM <| auditConstants
      (`Palamedes.Data).isPrefixOf
      "someSupport inventory found no `support_` lemmas; are the `Data` modules imported?"
      fun n => do
      let .str ns s := n | return false
      unless s.startsWith "support_" do return false
      if s.endsWith "_congr" || exemptCaseSplits.contains n then return false
      let twin := Name.str ns ("someSupport_" ++ (s.drop "support_".length).toString)
      let some twinInfo := (← getEnv).find? twin
        | logError m!"{n} has no `someSupport` twin ({twin}): the first filtering `@[correct]` \
            whose generator uses this primitive will fail at the law bridge. Add the twin beside \
            the `support_` lemma (see `Data/Nat.lean` for the pattern)."
          return true
      -- The twin must state a rewrite whose left side is *about* `someSupport` — that is what the
      -- bridge's simp set fires on. A lemma that merely carries the name rewrites nothing. Both
      -- shapes in use qualify: `someSupport g = P`, and the pointwise `someSupport g v ↔ …` that a
      -- membership characterization takes.
      let ok ← forallTelescope twinInfo.type fun _ body => do
        let lhs? := (body.eq?.map (·.2.1)) <|> (body.iff?.map (·.1))
        return (lhs?.map (·.isAppOf ``Palamedes.someSupport)).getD false
      unless ok do
        logError m!"{twin} does not rewrite `someSupport`, so it cannot discharge the law bridge \
          for {n} even though it is named as its twin."
      return true

end PalamedesTest.SomeSupport
