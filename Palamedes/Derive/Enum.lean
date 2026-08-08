/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Derive.Util

/-!
# The finite-enumeration generator layer

`derive_enum_gen X` generates the uniform draw layer for an enumeration: `arbX`, its
support/`someSupport`/totality facts, the synthesis rule `s_arbX`, and the recursor rule
`total_X_rec`. Case analysis is *not* part of it — a `@[case_split]` rule is hand-written per
datatype, because the shape that keeps the search finding the same generator differs from type to
type.
-/

open Lean Elab Command Meta
open Lean.Parser.Term (matchAltExpr matchAlt)
open Palamedes Palamedes.PGen Palamedes.PGen.Support

namespace Palamedes.Derive

/-- A finite enumeration being derived: the type, its nullary constructors, and whether the draw is
spelled at `TGen` behind an `@[irreducible]` `PGen` coercion. -/
structure EnumCtx where
  xName : Name
  ctors : Array Name
  /-- `true` spells the draw at `TGen` and marks its `PGen` form `@[irreducible]`, so the optimizer
  treats it as an opaque primitive and emitted terms name it instead of inlining its `pick`. -/
  primitive : Bool

def EnumCtx.short (ctx : EnumCtx) : String := ctx.xName.getString!
/-- The base name of the draw: `arbBool`, `arbColor`, … -/
def EnumCtx.arb (ctx : EnumCtx) : String := "arb" ++ ctx.short
def EnumCtx.xRef (ctx : EnumCtx) : Ident := rootedIdent ctx.xName
def EnumCtx.ctorRefs (ctx : EnumCtx) : Array Ident := ctx.ctors.map rootedIdent
def EnumCtx.pgenId (_ : EnumCtx) (s : String) : Ident :=
  rootedIdent (`Palamedes.PGen ++ Name.mkSimple s)
def EnumCtx.tgenId (_ : EnumCtx) (s : String) : Ident :=
  rootedIdent (`Palamedes.TGen ++ Name.mkSimple s)
def EnumCtx.correctId (_ : EnumCtx) (s : String) : Ident :=
  rootedIdent (`Palamedes.PGen.CorrectGen ++ Name.mkSimple s)
def EnumCtx.totalId (_ : EnumCtx) (s : String) : Ident :=
  rootedIdent (`Palamedes.PGen.Total ++ Name.mkSimple s)

/-- A right-nested application `op x₁ (op x₂ (… xₙ))` (`n ≥ 2`). -/
def mkChain (op : Ident) (xs : Array Term) : CommandElabM Term :=
  xs.pop.foldrM (fun t acc => `($op $t $acc)) xs.back!

/-- Builds an `EnumCtx` and rules out everything that is not a finite enumeration. -/
def analyzeEnum (xName : Name) (primitive : Bool) : CoreM EnumCtx := do
  let indVal ← getConstInfoInduct xName
  unless indVal.all.length == 1 do
    throwError "derive_enum_gen: mutual inductives are not supported"
  unless indVal.levelParams.isEmpty && indVal.numParams == 0 && indVal.numIndices == 0 do
    throwError "derive_enum_gen: {xName} takes universe parameters, parameters or indices, so it \
      is not a finite enumeration"
  unless indVal.type == .sort 1 do
    throwError "derive_enum_gen: only `Type`-valued inductives are supported"
  if indVal.ctors.length < 2 then
    throwError "derive_enum_gen: {xName} has fewer than two constructors, so there is no choice to \
      generate"
  for c in indVal.ctors do
    unless (← getConstInfoCtor c).numFields == 0 do
      throwError "derive_enum_gen: constructor {c} takes fields, so {xName} is not a finite \
        enumeration; use `derive_palamedes` instead"
  return { xName, ctors := indVal.ctors.toArray, primitive }

def genEnumArb (ctx : EnumCtx) : CommandElabM Unit := do
  let self := ctx.xRef
  let arbP := ctx.pgenId ctx.arb
  if ctx.primitive then
    let arbT := ctx.tgenId ctx.arb
    let branches ← ctx.ctorRefs.mapM fun c => `($(mkCIdent ``Palamedes.TGen.pure) $c)
    let body ← mkChain (mkCIdent ``Palamedes.TGen.pick) branches
    addCmd (← `(command|
      def $arbT:ident : $(mkCIdent ``Palamedes.TGen) $self := $body))
    addCmd (← `(command|
      @[irreducible] def $arbP:ident : $(mkCIdent ``Palamedes.PGen) $self :=
        $(mkCIdent ``Palamedes.TGen.toGen) $arbT))
  else
    let branches ← ctx.ctorRefs.mapM fun c => `($(mkCIdent ``Pure.pure) $c)
    let body ← mkChain (mkCIdent ``Palamedes.PGen.pick) branches
    addCmd (← `(command|
      def $arbP:ident : $(mkCIdent ``Palamedes.PGen) $self := $body))

/-- `support_arbX` / `someSupport_arbX`: the draw covers the whole type. -/
def genEnumSupport (ctx : EnumCtx) (someSupport : Bool) : CommandElabM Unit := do
  let v := gid "v"
  let head := if someSupport then mkCIdent ``Palamedes.someSupport
              else mkCIdent ``Palamedes.PGen.support
  let nm := (if someSupport then "someSupport_" else "support_") ++ ctx.arb
  let unfolds : Array Term :=
    if ctx.primitive then #[ctx.pgenId ctx.arb, ctx.tgenId ctx.arb] else #[ctx.pgenId ctx.arb]
  addCmd (← `(command|
    @[simp] theorem $(ctx.pgenId nm):ident :
        $head $(ctx.pgenId ctx.arb) = fun _ => True := by
      funext $v:ident
      cases $v:ident <;> simp_all [$[$unfolds:term],*]))

def genEnumSArb (ctx : EnumCtx) : CommandElabM Unit := do
  let v := gid "v"
  addCmd (← `(command|
    @[extract, aesop safe apply (rule_sets := [synthesis])]
    def $(ctx.correctId ("s_" ++ ctx.arb)):ident :
        @$(mkCIdent ``Palamedes.CorrectGen) $(ctx.xRef) (fun _ => True) :=
      Subtype.mk $(ctx.pgenId ctx.arb) (by funext $v:ident; simp)))

/-- `total_arbX`. In `primitive` mode the witness is the `TGen` definition itself and the `unfold`
stays in the **proof** component: written `by unfold arbX; exact …` instead, the whole term sits
under an `Eq.mpr` in the data path, `.val` stops projecting, and the witness reaches the environment
as a proof term. -/
def genEnumTotalArb (ctx : EnumCtx) : CommandElabM Unit := do
  let nm := ctx.totalId ("total_" ++ ctx.arb)
  let arbP := ctx.pgenId ctx.arb
  if ctx.primitive then
    addCmd (← `(command|
      @[total] def $nm:ident : $(mkCIdent ``Palamedes.PGen.total) $arbP :=
        ⟨$(ctx.tgenId ctx.arb), by unfold $arbP:ident; rfl⟩))
  else
    let branches ← ctx.ctors.mapM fun _ => `($(mkCIdent ``Palamedes.PGen.Total.total_pure) _)
    let body ← mkChain (mkCIdent ``Palamedes.PGen.Total.total_pick) branches
    addCmd (← `(command|
      @[total] def $nm:ident :
          $(mkCIdent ``Palamedes.PGen.total)
            ($arbP : $(mkCIdent ``Palamedes.PGen) $(ctx.xRef)) := $body))

/-- `total_X_rec`, keyed on `X.rec` because that is what the totality descent dispatches on.

The case split stays **inside** `TGen.mk` (see `total_dite`), and the data is a `match`, not the
recursor: `by cases x <;> assumption` puts `X.rec` in the data path, where `.val` cannot project
past it until the scrutinee is concrete, and the code generator rejects a bare recursor anyway. -/
def genEnumTotalRec (ctx : EnumCtx) : CommandElabM Unit := do
  let α := gid "α"
  let x := gid "x"
  let gs := ctx.ctors.map fun c => gid s!"g_{c.getString!}"
  let hs := ctx.ctors.map fun c => gid s!"h_{c.getString!}"
  let pgenα ← `($(mkCIdent ``Palamedes.PGen) $α)
  let mut binders : Array BB := #[
    ← impB #[α] (← `(Type)), ← impB gs pgenα, ← impB #[x] (ctx.xRef : Term)]
  for g in gs, h in hs do
    binders := binders.push (← expB h (← `($(mkCIdent ``Palamedes.PGen.total) $g)))
  let witAlts ← ctx.ctorRefs.mapIdxM fun i c =>
    `(matchAltExpr| | $c:term => ($(hs[i]!)).val.run)
  let arms ← hs.mapM fun h => `(tactic| exact ($h).property)
  addCmd (← `(command|
    @[total]
    def $(ctx.totalId s!"total_{ctx.short}_rec"):ident $binders:bracketedBinder* :
        $(mkCIdent ``Palamedes.PGen.total) ($(rootedIdent (ctx.xName ++ `rec)) $gs* $x) :=
      ⟨⟨fun {_G} _ => match $x:ident with $witAlts:matchAlt*⟩,
       by cases $x:ident <;> first $[| $arms:tactic]*⟩))

/-- `derive_enum_gen X` generates the draw layer for the finite enumeration `X`; the `primitive`
modifier spells the draw at `TGen` behind an `@[irreducible]` `PGen` coercion, so emitted terms name
it (`TGen.arbLabel.run`) instead of inlining its `pick` at every use site. -/
syntax (name := deriveEnumGen) "derive_enum_gen " ident (&"primitive")? : command

@[command_elab deriveEnumGen]
def elabDeriveEnumGen : CommandElab := fun stx => do
  let xName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let ctx ← liftCoreM <| analyzeEnum xName (primitive := !stx[2].isNone)
  genEnumArb ctx
  genEnumSupport ctx (someSupport := false)
  genEnumSupport ctx (someSupport := true)
  genEnumSArb ctx
  genEnumTotalArb ctx
  genEnumTotalRec ctx

end Palamedes.Derive
