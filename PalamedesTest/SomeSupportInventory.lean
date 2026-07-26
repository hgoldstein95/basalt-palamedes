/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes

/-!
# `someSupport` twin inventory

Every hand-written primitive pays a standing tax: its `support_X` characterization needs a
`someSupport_X` twin, or the first *filtering* `@[correct]` whose generator uses the primitive
fails at the law bridge (`CorrectDef` discharges `someSupport g = P` by simp over the twins). The
tax is per-primitive and easy to forget precisely because nothing consumes the twin until a
filtering generator happens to reach it — the gap is silent until someone else's `@[correct]`
breaks.

This module makes the gap loud instead: it walks every `support_*` lemma in `Palamedes/Data/` and
*fails to compile* if the `someSupport_*` twin next to it is missing, or if the twin does not
actually characterize `someSupport` — a conventionally-named lemma stating something else would
otherwise satisfy a name-only check while leaving the bridge just as broken.

Exempt: `*_congr` lemmas and case-split combinators (`support_Ty_caseTy` &c.), which state
*relative* facts rather than characterizations, so there is no `someSupport` reading to demand.
(Case-split twins are a known residual of the same kind — no filtering generator cases on a derived
type today, and the bridge will name the missing lemma if one ever does.)
-/

open Lean Meta Elab Command

namespace PalamedesTest.SomeSupportInventory

run_cmd liftTermElabM do
  let env ← getEnv
  let mut total := 0
  for i in [0:env.header.moduleData.size] do
    let modName := env.header.moduleNames[i]!
    unless (`Palamedes.Data).isPrefixOf modName do continue
    for n in env.header.moduleData[i]!.constNames do
      let .str ns s := n | continue
      unless s.startsWith "support_" do continue
      let x := (s.drop "support_".length).toString
      if s.endsWith "_congr" || (x.toLower.splitOn "case").length > 1 then continue
      total := total + 1
      let twin := Name.str ns ("someSupport_" ++ x)
      let some twinInfo := env.find? twin
        | logError m!"{n} has no `someSupport` twin ({twin}): the first filtering `@[correct]` \
            whose generator uses this primitive will fail at the law bridge. Add the twin beside \
            the `support_` lemma (see `Data/Nat.lean` for the pattern)."
          continue
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
  if total == 0 then
    logError "someSupport inventory found no `support_` lemmas; are the `Data` modules imported?"

end PalamedesTest.SomeSupportInventory
