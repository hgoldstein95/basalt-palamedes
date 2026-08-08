/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Derive.Util

/-!
# The Base Functor `XF`

Generated at the `Expr` level as a `Declaration.inductDecl`, together with the auxiliary
constructions the `inductive` frontend would otherwise emit, since tactics run on `XF` values
downstream expect them to be there.
-/

open Lean Elab Command Meta
open Lean.Parser.Term (matchAltExpr matchAlt)
open Palamedes Palamedes.PGen Palamedes.PGen.Support

namespace Palamedes.Derive

/-- Make the first `n` `∀`-binders implicit. Kernel constructor types bind parameters explicitly,
while the `inductive` frontend marks them implicit, so a hand-built `inductDecl` has to match. -/
def mkImplicitPrefix : Nat → Expr → Expr
  | 0, e => e
  | n + 1, .forallE nm t b _ => .forallE nm t (mkImplicitPrefix n b) .implicit
  | _, e => e

/-- Generate the base functor `XF` at the `Expr` level (`Declaration.inductDecl`): the same
constructors, with every recursive occurrence replaced by a fresh carrier `β`. -/
def genBaseFunctor (xName fName : Name) : TermElabM Unit := do
  let indVal ← getConstInfoInduct xName
  let lvls := indVal.levelParams.map fun _ => Level.zero
  forallBoundedTelescope (indVal.type.instantiateLevelParams indVal.levelParams lvls)
      indVal.numParams fun params _ => do
    withLocalDeclD `β (.sort 1) fun β => do
      let fType ← mkForallFVars (params.push β) (.sort 1)
      let resTy := mkAppN (mkConst fName) (params.push β)
      let ctors ← indVal.ctors.mapM fun ctorName => do
        let ctorInfo ← getConstInfoCtor ctorName
        let ty ← instantiateForall (ctorInfo.type.instantiateLevelParams ctorInfo.levelParams lvls)
          params
        forallTelescope ty fun fields _ => do
          let rec go (i : Nat) (acc : Array Expr) : MetaM Expr := do
            if h : i < fields.size then
              let f := fields[i]
              let t ← inferType f
              let t := t.replaceFVars (fields.extract 0 i) acc
              let t := if t.getAppFn.isConstOf xName then β else t
              withLocalDeclD (← f.fvarId!.getUserName) t fun x => go (i + 1) (acc.push x)
            else
              mkForallFVars (params.push β ++ acc) resTy
          let ctorTy := mkImplicitPrefix (indVal.numParams + 1) (← go 0 #[])
          pure { name := fName ++ ctorName.getString!.toName, type := ctorTy : Constructor }
      let decl := Declaration.inductDecl [] (indVal.numParams + 1)
        [{ name := fName, type := fType, ctors := ctors : InductiveType }] false
      addDecl decl
      Lean.compileDecls #[fName]
      mkRecOn fName
      mkCasesOn fName
      mkCtorIdx fName
      mkCtorElim fName
      mkNoConfusion fName
      mkBelow fName
      mkBRecOn fName
      Lean.Meta.mkInjectiveTheorems fName

end Palamedes.Derive
