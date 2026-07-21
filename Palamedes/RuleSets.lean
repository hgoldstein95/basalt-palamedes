import Lean
import Aesop

/-!
# Rule registries

Two tag-driven registries, so that adding a datatype needs no synthesizer edit: the `synthesis`
Aesop rule set (the search in `Synthesizer/CGeneratorSearch.lean`), and `@[total]`, the per-datatype
rules the `totality` tactic reconstructs a `TGen` witness from.

`@[total]` is deliberately *not* an Aesop rule set: `totality` is an ordered cascade, not a search.
Only the part of it whose order does not matter lives here — see `Synthesizer/Totality.lean`.
-/

declare_aesop_rule_sets [synthesis]

open Lean

namespace Palamedes

initialize totalExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.flatten
  }

/-- Every `@[total]`-tagged lemma, in registration order. -/
def totalLemmas (env : Environment) : Array Name := totalExt.getState env

initialize registerBuiltinAttribute {
  name := `total
  descr := "register a per-datatype totality rule; the `totality` tactic tries it via `apply`"
  add := fun declName stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    unless kind == .global do
      throwError "@[total] must be global"
    -- Reject a mistagged lemma here; otherwise it surfaces as an opaque failure inside the tactic's
    -- `first | …` cascade. (A `Name` literal, not a `` `` `` one: `PGen.total` lives in a module that
    -- imports this one, so the constant does not exist yet when this file elaborates.)
    let info ← getConstInfo declName
    let ok ← Lean.Meta.MetaM.run' <| Lean.Meta.forallTelescope info.type fun _ concl =>
      return concl.getAppFn.isConstOf `Palamedes.PGen.total
    unless ok do
      throwError "@[total]: `{declName}` does not conclude in `Palamedes.PGen.total _`, so the \
        `totality` tactic could never apply it"
    modifyEnv fun env => totalExt.addEntry env declName
}

end Palamedes
