/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Lean

/-!
# The `case_split` registry

The datatypes `caseSplitRuleTac` can scrutinise, each paired with its `s_case*` lemma, live in a
persistent environment extension keyed by the scrutinee's datatype. Tag the lemma at its
definition site — alongside `@[extract]`, which is what pulls the raw `PGen` back out of the
`CorrectGen` the rule builds (every real registration carries both):

```
@[extract, case_split]
def s_caseBool (b : Bool) (h : ∀ {a}, P a b = Q a) … : CorrectGen Q := …
```

The scrutinee datatype is read off the lemma's signature — the head constant of the first
explicit argument's type — so the attribute takes no arguments.
-/

open Lean Meta

namespace Palamedes

initialize caseSplitExt :
    SimplePersistentEnvExtension (Name × Name) (Array (Name × Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.flatten
  }

/-- All registered `(datatype, s_case lemma)` pairs, in registration order. -/
def caseSplitLemmas (env : Environment) : Array (Name × Name) :=
  caseSplitExt.getState env

initialize registerBuiltinAttribute {
  name := `case_split
  descr := "register an `s_case*` lemma for the case-split synthesis rule, keyed by the \
    datatype of its scrutinee (the first explicit argument)"
  add := fun declName stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    unless kind == .global do
      throwError "@[case_split] must be global"
    let info ← getConstInfo declName
    let typeName ← MetaM.run' <| forallTelescope info.type fun args concl => do
      -- A `Name` literal, not a `` `` `` one: `Palamedes.CorrectGen` is declared in a module that
      -- imports this one, so the constant does not exist yet here.
      unless (← whnfR concl).isAppOf `Palamedes.CorrectGen do
        throwError "@[case_split]: {declName} concludes in {concl}, not in `CorrectGen _`, so the \
          case-split rule could never apply it"
      for arg in args do
        if (← arg.fvarId!.getBinderInfo).isExplicit then
          let scrutTy ← whnfR (← inferType arg)
          let .const typeName _ := scrutTy.getAppFn
            | throwError "@[case_split]: the first explicit argument of {declName} has type \
                {scrutTy}, whose head is not a constant"
          return typeName
      throwError "@[case_split]: {declName} has no explicit scrutinee argument"
    -- One lemma per datatype, checked at tag time: the rule selects by datatype and keeps the first
    -- match, so a second registration would be silently unreachable.
    for (prevTy, prevDecl) in caseSplitLemmas (← getEnv) do
      if prevTy == typeName then
        throwError "@[case_split]: {declName} and {prevDecl} both case-split on {typeName}, so the \
          case-split rule would have to choose between them. Keep one, or give them distinct \
          scrutinee types."
    modifyEnv fun env => caseSplitExt.addEntry env (typeName, declName)
}

end Palamedes
