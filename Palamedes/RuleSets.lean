/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Lean
import Aesop

/-!
# Rule registries

Two tag-driven registries, so that adding a datatype needs no synthesizer edit: the `synthesis`
Aesop rule set (the search in `Synthesizer/CGeneratorSearch.lean`), and `@[total]`, the rules the
`totality` tactic reconstructs a `TGen` witness from.

`@[total]` is deliberately *not* an Aesop rule set: `totality` is a **structural descent**, not a
search. Every registered rule is keyed by the head constant it reconstructs (`totalKey?` below), so
dispatch is a lookup rather than a `first | apply …` race, and the whole basis — the generic
combinators as much as the per-datatype leaves — lives in this one registry. Two consequences that
used to be hazards:

* **Order cannot matter.** `total_oneOf` and `total_frequency` used to have to be tried in that
  order, since `oneOf` *is* a `frequency` and `apply` would let the latter capture the former's
  goal. Keyed dispatch sees `PGen.oneOf` and `PGen.frequency` as different heads.
* **A tagged rule cannot be unreachable.** The tactic used to re-list most of the basis by hand and
  had already drifted once (`total_color_rec` was tagged but missing, and survived only because a
  `simp` fallback happened to catch it). The tag *is* the registration now, and a second rule
  claiming a head already claimed is rejected at tag time rather than silently shadowed.
-/

declare_aesop_rule_sets [synthesis]

open Lean

namespace Palamedes

/-- A registered totality rule and the goal shape it reconstructs.

The key is stored rather than recomputed. Deriving it needs `forallTelescope` + `matchMatcherApp?`
per rule, and the descent looks a rule up at *every node of every generator* — recomputing there
would put the whole registry inside the inner loop. Tag time is also where the key has to be known
anyway, for the one-rule-per-head check. -/
structure TotalRule where
  /-- `Palamedes.PGen.total`, `…totalList`, or `…totalWeighted`. -/
  goal : Name
  /-- The head constant reconstructed: a combinator, or a base functor for a `match` node. -/
  head : Name
  decl : Name
  deriving Inhabited, BEq, Repr

initialize totalExt : SimplePersistentEnvExtension TotalRule (Array TotalRule) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.flatten
  }

/-- Every `@[total]`-tagged rule, in registration order. -/
def totalRules (env : Environment) : Array TotalRule := totalExt.getState env

/-- The declaration names of every `@[total]`-tagged rule, in registration order. -/
def totalLemmas (env : Environment) : Array Name := (totalRules env).map (·.decl)

/-- The registry as the descent's dispatch table, keyed as `totalKey?` keys a goal. -/
def totalTable (env : Environment) : Std.HashMap (Name × Name) Name :=
  (totalRules env).foldl (init := {}) fun m r => m.insert (r.goal, r.head) r.decl

/-- The three goal shapes the totality descent dispatches on. (`Name` literals, not `` `` `` ones:
these live in a module that imports this one, so the constants do not exist yet here.) -/
private def totalGoalHeads : List Name :=
  [`Palamedes.PGen.total, `Palamedes.PGen.totalList, `Palamedes.PGen.totalWeighted]

/-- What a totality goal dispatches on: the goal's own head paired with the head constant of the
generator (or branch list) it is about. `none` if `concl` is not a totality goal at all.

A `match` node is keyed by its **discriminant's type** rather than by the matcher constant. The
matcher in a synthesized generator need not be the same auxiliary as the one in `X.total_cases`'s
statement — matchers are per-elaboration and only defeq, which is why `apply` used to be the thing
doing the matching — but the base functor is the same either way, and there is exactly one
`total_cases` per base functor.

The argument is `headBeta`'d and nothing else: no `whnf`. Delta-unfolding here would defeat the
point, turning `PGen.oneOf` into the `PGen.frequency` it is defined as and reinstating the very
collision keyed dispatch exists to rule out. -/
def totalKey? (concl : Expr) : MetaM (Option (Name × Name)) := do
  let some goal := concl.getAppFn.constName? | return none
  unless totalGoalHeads.contains goal do return none
  let arg := concl.appArg!.headBeta
  if let some app ← Lean.Meta.matchMatcherApp? arg then
    if let some d := app.discrs[0]? then
      -- `instantiateMVars`, and not because the goal was not instantiated: the discriminant is an
      -- fvar, and its *type in the local context* is whatever it was when the binder was
      -- introduced — here an mvar the descent has since assigned. Reading it raw gets `?m`, the
      -- match branch is skipped, and dispatch silently falls back to the matcher constant, which no
      -- rule is keyed by. The symptom is a `casesOn` in the emitted generator, three stages away.
      let dty ← instantiateMVars (← Lean.Meta.inferType d)
      if let some ty := dty.consumeMData.getAppFn.constName? then
        return some (goal, ty)
  return arg.getAppFn.constName?.map (goal, ·)

/-- `totalKey?` of a rule's conclusion, under its telescope. -/
def totalRuleKey? (declName : Name) : CoreM (Option (Name × Name)) := do
  let info ← getConstInfo declName
  Lean.Meta.MetaM.run' <| Lean.Meta.forallTelescope info.type fun _ concl => totalKey? concl

initialize registerBuiltinAttribute {
  name := `total
  descr := "register a totality rule, keyed by the head constant it reconstructs; the `totality` \
    tactic dispatches on that key"
  add := fun declName stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    unless kind == .global do
      throwError "@[total] must be global"
    -- Reject a mistagged rule here; otherwise it is simply never dispatched to, which is silent.
    let some key ← totalRuleKey? declName
      | throwError "@[total]: `{declName}` does not conclude in `Palamedes.PGen.total _` (nor \
          `totalList`/`totalWeighted`) applied to something with a head constant, so the \
          `totality` tactic could never dispatch to it"
    -- One rule per head, checked at tag time. This is what makes the ordering hazard structural
    -- rather than a comment: two rules that could race are now a build error naming both.
    for prev in totalRules (← getEnv) do
      if (prev.goal, prev.head) == key then
        throwError "@[total]: `{declName}` and `{prev.decl}` both reconstruct `{key.2}`, so the \
          `totality` tactic would have to choose between them. Keep one, or give them distinct \
          heads."
    modifyEnv fun env =>
      totalExt.addEntry env { goal := key.1, head := key.2, decl := declName }
}

end Palamedes
