/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Lean
import Aesop

/-!
# Rule Registries

Tag-driven registries that allow users to support their own datatypes without editing the
synthesizer.
-/

declare_aesop_rule_sets [synthesis]

open Lean

namespace Palamedes

/-- A registered totality rule and the goal shape it reconstructs. -/
structure TotalRule where
  /-- `Palamedes.PGen.total`, `…totalList`, or `…totalWeighted`. -/
  goal : Name
  /-- The head constant reconstructed: a combinator, or a base functor for a `match` node. -/
  head : Name
  decl : Name
  deriving Inhabited, BEq, Repr

/-- The registry state: the rules in registration order, and the same rules as the descent's
dispatch table. These are maintained together to make lookup cheaper. -/
structure TotalRuleSet where
  rules : Array TotalRule := #[]
  /-- Keyed as `totalKey?` keys a goal. -/
  table : Std.HashMap (Name × Name) Name := {}

instance : Inhabited TotalRuleSet := ⟨{}⟩

def TotalRuleSet.insert (s : TotalRuleSet) (r : TotalRule) : TotalRuleSet :=
  { rules := s.rules.push r, table := s.table.insert (r.goal, r.head) r.decl }

initialize totalExt : SimplePersistentEnvExtension TotalRule TotalRuleSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := TotalRuleSet.insert
    addImportedFn := fun ess => ess.flatten.foldl TotalRuleSet.insert {}
  }

/-- Every `@[total]`-tagged rule, in registration order. -/
def totalRules (env : Environment) : Array TotalRule := (totalExt.getState env).rules

/-- The declaration names of every `@[total]`-tagged rule, in registration order. -/
def totalLemmas (env : Environment) : Array Name := (totalRules env).map (·.decl)

/-- The registry as the descent's dispatch table, keyed as `totalKey?` keys a goal. -/
def totalTable (env : Environment) : Std.HashMap (Name × Name) Name := (totalExt.getState env).table

/-- The three goal shapes the totality descent dispatches on. (`Name` literals, not `` `` `` ones:
these live in a module that imports this one, so the constants do not exist yet here.) -/
private def totalGoalHeads : List Name :=
  [`Palamedes.PGen.total, `Palamedes.PGen.totalList, `Palamedes.PGen.totalWeighted]

/-- What a totality goal dispatches on: the goal's own head paired with the head constant of the
generator (or branch list) it is about. `none` if `concl` is not a totality goal at all. -/
def totalKey? (concl : Expr) : MetaM (Option (Name × Name)) := do
  let some goal := concl.getAppFn.constName? | return none
  unless totalGoalHeads.contains goal do return none
  -- The argument is `headBeta`'d, not `whnf`. Delta-unfolding here would turn `PGen.oneOf` into
  -- `PGen.frequency`.
  let arg := concl.appArg!.headBeta
  if let some app ← Lean.Meta.matchMatcherApp? arg then
    if let some d := app.discrs[0]? then
      -- The discriminant is an fvar whose *type in the local context* is whatever it was when the
      -- binder was introduced — typically an mvar the descent has since assigned. Read raw that is
      -- `?m`, so the match branch is skipped and dispatch falls back to the matcher constant, which
      -- no rule is keyed by; the symptom is a `casesOn` in the emitted generator, three stages away.
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
    -- One rule per head, checked at tag time: two rules that could race are a build error naming
    -- both.
    if let some prev := (totalTable (← getEnv))[key]? then
      throwError "@[total]: `{declName}` and `{prev}` both reconstruct `{key.2}`, so the \
        `totality` tactic would have to choose between them. Keep one, or give them distinct \
        heads."
    modifyEnv fun env =>
      totalExt.addEntry env { goal := key.1, head := key.2, decl := declName }
}

end Palamedes
