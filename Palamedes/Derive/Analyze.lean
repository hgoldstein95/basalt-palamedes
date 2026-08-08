/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Derive.Util

/-!
# Initial Datatype Analysis
-/

open Lean Elab Command Meta
open Lean.Parser.Term (matchAltExpr matchAlt)
open Palamedes Palamedes.PGen Palamedes.PGen.Support

namespace Palamedes.Derive

/-- Builds a `Ctx` from a datatype name and rules out unsupported shapes (mutual, indexed and nested
inductives, non-`Type` parameters, dependent constructor fields).  -/
def analyze (xName : Name) : TermElabM Ctx := do
  let indVal ← getConstInfoInduct xName
  unless indVal.all.length == 1 do
    throwError "derive_palamedes: mutual inductives are not supported"
  unless indVal.numIndices == 0 do
    throwError "derive_palamedes: indexed inductives are not supported"
  if indVal.isNested then
    throwError "derive_palamedes: nested inductives are not supported"
  if indVal.ctors.isEmpty then
    throwError "derive_palamedes: {xName} has no constructors, so there is nothing to generate"
  -- Universe-polymorphic inductives (e.g. core `List`) are instantiated at universe 0: the whole
  -- generated template is `Type`-monomorphic anyway, matching the hand-written modules.
  let lvls := indVal.levelParams.map fun _ => Level.zero
  let fName := xName.appendAfter "F"
  forallBoundedTelescope (indVal.type.instantiateLevelParams indVal.levelParams lvls)
      indVal.numParams fun params bodyTy => do
    unless bodyTy == .sort 1 do
      throwError "derive_palamedes: only `Type`-valued inductives are supported"
    let mut paramIds := #[]
    for p in params do
      unless (← inferType p) == .sort 1 do
        throwError "derive_palamedes: parameters must have type `Type`"
      paramIds := paramIds.push (mkIdent (← p.fvarId!.getUserName))
    let selfE := mkAppN (mkConst xName lvls) params
    let mut ctors := #[]
    for cn in indVal.ctors do
      let ci ← getConstInfoCtor cn
      let ty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams lvls) params
      let fds ← forallTelescope ty fun fs _ => do
        let mut fds : Array FieldData := #[]
        for h : i in [0:fs.size] do
          let f := fs[i]
          let t ← inferType f
          for j in [0:i] do
            if t.containsFVar fs[j]!.fvarId! then
              throwError "derive_palamedes: dependent constructor fields are not supported ({cn})"
          let isRec := t.getAppFn.isConstOf xName
          if isRec then
            unless t == selfE do
              throwError "derive_palamedes: only direct recursive occurrences are supported ({cn})"
          else
            if (t.find? (·.isConstOf xName)).isSome then
              throwError "derive_palamedes: nested/indirect recursion is not supported ({cn})"
          let tyStx ← PrettyPrinter.delab t
          fds := fds.push { id := mkIdent (Name.mkSimple s!"a{i+1}"), isRec, tyStx }
        pure fds
      ctors := ctors.push
        { xCtor := rootedIdent cn
          fCtor := rootedIdent (fName ++ Name.mkSimple cn.getString!)
          short := Name.mkSimple cn.getString!
          injName := cn ++ `inj
          fields := fds }
    pure { xName, fName, paramIds, ctors }

end Palamedes.Derive
