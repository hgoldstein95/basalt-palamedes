import Lean

/-!
# The `case_split` registry

The datatypes `caseSplitRuleTac` can scrutinise, each paired with its `s_case*` lemma, live in a
persistent environment extension keyed by the scrutinee's datatype. Tag the lemma at its
definition site:

```
@[case_split]
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
  add := fun declName _stx kind => do
    unless kind == .global do
      throwError "@[case_split] must be global"
    let info ← getConstInfo declName
    let typeName ← MetaM.run' <| forallTelescope info.type fun args _ => do
      for arg in args do
        if (← arg.fvarId!.getBinderInfo).isExplicit then
          let scrutTy ← whnfR (← inferType arg)
          let .const typeName _ := scrutTy.getAppFn
            | throwError "@[case_split]: the first explicit argument of {declName} has type \
                {scrutTy}, whose head is not a constant"
          return typeName
      throwError "@[case_split]: {declName} has no explicit scrutinee argument"
    modifyEnv fun env => caseSplitExt.addEntry env (typeName, declName)
}

end Palamedes
