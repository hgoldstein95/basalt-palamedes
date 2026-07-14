import Lean

/-!
# The `unfold_strategy` registry

The per-datatype data that `normalize_and_apply_unfold` used to hard-code — which `s_unfold` to
apply, and which fold/coercion/merge/conversion lemmas to normalize with — lives in a persistent
environment extension keyed by the datatype name. `derive_palamedes` registers the standard entry
for every type it derives, so a new datatype needs **no synthesizer edits** to participate in unfold
synthesis. (Totality is the sibling registry: `X.total_unfold` is tagged `@[total]` and read by the
`totality` tactic — see `Palamedes.RuleSets`.)

Two commands amend an entry with the hand-written extras the derive command deliberately does
not generate:

* `unfold_strategy_cond X X.fold_accu_cond` — set the conditional-fold normal form
  (`norm_for_unfold`'s `condVia` step);
* `unfold_strategy_convert X X.fold_accu_Option_extra` — insert an additional conversion lemma
  into the `convertVia` list, just before the final (most permissive) `_basic` entry.
-/

open Lean

namespace Palamedes

structure UnfoldStrategy where
  /-- The datatype this entry synthesizes unfolds for. -/
  typeName : Name
  /-- The `CorrectGen` combinator applied to the goal (`X.s_unfold`). -/
  sUnfold : Name
  /-- `X.fold` (used by `goal_is_not_fold` to detect already-normalized predicates). -/
  fold : Name
  /-- `X.coerce_to_fold`. -/
  coerce : Name
  /-- The banana-split merge lemma (`X.merge_accuM`). -/
  merge : Name
  /-- The `fold_accu_Option_*` conversion lemmas, tried in order. -/
  convert : Array Name
  /-- `X.unfold` itself, so the optimizer can recognize a recursion in the term it is rewriting. -/
  unfoldName : Name
  /-- The conditional-fold normal form (`X.fold_accu_cond`), if the type has one. -/
  cond : Option Name := none
  deriving Inhabited, Repr

initialize unfoldStrategyExt :
    SimplePersistentEnvExtension UnfoldStrategy (Array UnfoldStrategy) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.flatten
  }

/-- All registered strategies, in registration order. An entry re-registered later (e.g. amended
by `unfold_strategy_cond`) supersedes the earlier one for the same type. -/
def unfoldStrategies (env : Environment) : Array UnfoldStrategy := Id.run do
  let raw := unfoldStrategyExt.getState env
  let mut seen : NameSet := {}
  let mut out := #[]
  -- keep only the LAST entry per type, preserving first-registration order
  for e in raw.reverse do
    unless seen.contains e.typeName do
      seen := seen.insert e.typeName
      out := out.push e
  return out.reverse

def registerUnfoldStrategy (entry : UnfoldStrategy) : CoreM Unit :=
  modifyEnv fun env => unfoldStrategyExt.addEntry env entry

/-- Map from each registered `X.unfold` constant to its datatype, so a traversal can tell when it
is descending into a recursion. -/
def unfoldNameMap (env : Environment) : Std.HashMap Name Name :=
  (unfoldStrategies env).foldl (init := {}) fun m e => m.insert e.unfoldName e.typeName

private def getStrategyFor (env : Environment) (typeName : Name) : CoreM UnfoldStrategy := do
  let some e := (unfoldStrategies env).find? (·.typeName == typeName)
    | throwError "no unfold_strategy entry registered for {typeName} (is it `derive_palamedes`d?)"
  return e

open Elab Command in
/-- `unfold_strategy_cond X lem` sets `lem` as `X`'s conditional-fold normal form. -/
elab "unfold_strategy_cond " t:ident l:ident : command => do
  let tn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  let ln ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo l
  liftCoreM do
    let e ← getStrategyFor (← getEnv) tn
    registerUnfoldStrategy { e with cond := some ln }

open Elab Command in
/-- `unfold_strategy_convert X lem` inserts `lem` into `X`'s `convertVia` list, just before the
final (most permissive) entry. -/
elab "unfold_strategy_convert " t:ident l:ident : command => do
  let tn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo t
  let ln ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo l
  liftCoreM do
    let e ← getStrategyFor (← getEnv) tn
    let convert :=
      if e.convert.isEmpty then #[ln]
      else (e.convert.pop.push ln).push e.convert.back!
    registerUnfoldStrategy { e with convert }

end Palamedes
