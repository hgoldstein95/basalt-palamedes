/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Lean
import Palamedes.PGen
import Palamedes.Support
import Palamedes.SomeSupport
import Palamedes.CorrectGen
import Palamedes.Total
import Palamedes.OptimizeCongr
import Palamedes.RuleSets
import Palamedes.UnfoldStrategy
import Palamedes.Util

/-!
# `derive_palamedes`: derive Palamedes' per-datatype boilerplate

`derive_palamedes X` generates, for a directly-recursive inductive `X`, the recursion-scheme
layer that `Palamedes/Data/` currently writes by hand:

* the base functor `XF` (recursive occurrences replaced by a carrier `β`);
* `X.fold` with per-constructor `@[simp]` equations (proved by `rfl`);
* `X.accuM` — the state-threading monadic fold — with per-constructor `@[simp]` equations;
* `X.unfoldGo` (a `partial_fixpoint` over Basalt's CCPO), `X.unfold`, the failure-free
  `TGen.X.unfold`, and `X.run_unfold`;
* `X.unfold_support` and the support characterization `X.support_unfold` (proved by a
  generated structural induction mirroring the hand-written proofs in `Data/`);
* `@[gen_congr] X.support_unfold_congr`;
* `X.total_unfold`, tagged into the `totality` aesop rule set;
* `X.coerce_to_fold` with per-constructor autoparam hypotheses.

The fusion layer is also generated: `merge_accuM` (banana split in the
`Option` monad), the `fold_accu_Option_{basic,true,function,function_true}` conversion family
(generalized per constructor: one `g_c`/`st_c{j}` and one shape hypothesis per recursive
constructor, subsuming the hand-written per-type variants), and the `CorrectGen` combinator
`s_unfold` with its `@[extract]` `s_unfold_val`. Not generated: `fold_accu_cond` (a search
heuristic's normal form) and `toString`.

Restrictions (rejected with an error): mutual, nested, and indexed inductives; non-`Type`
parameters; dependent constructor fields. Universe-polymorphic inductives (e.g. core `List`)
are accepted and instantiated at universe 0. Constructor argument order
in generated declarations follows declaration order (`f_leaf` before `f_node`), with one
`st_c`/`f_c` argument per constructor named after it.

Debugging: `set_option trace.Palamedes.derive true` prints every generated command.
-/

open Lean Elab Command Meta
open Lean.Parser.Term (matchAltExpr matchAlt)
open Palamedes Palamedes.PGen Palamedes.PGen.Support

namespace Palamedes.Derive

initialize registerTraceClass `Palamedes.derive

-- 0-ary parser aliases usable as quotation kinds (the raw parsers take arguments)
def implicitBinderF := Lean.Parser.Term.implicitBinder
def explicitBinderF := Lean.Parser.Term.explicitBinder
def instBinderF := Lean.Parser.Term.instBinder

abbrev BB := TSyntax ``Lean.Parser.Term.bracketedBinder

def impB (ids : Array Ident) (ty : Term) : CommandElabM BB := do
  return ⟨(← `(implicitBinderF| {$ids* : $ty})).raw⟩

def expB (id : Ident) (ty : Term) : CommandElabM BB := do
  return ⟨(← `(explicitBinderF| ($id : $ty))).raw⟩

def instBn (ty : Term) : CommandElabM BB := do
  return ⟨(← `(instBinderF| [$ty])).raw⟩

def mkArrows (tys : Array Term) (last : Term) : CommandElabM Term :=
  tys.foldrM (fun t acc => `($t → $acc)) last

def mkAnds (ps : Array Term) : CommandElabM Term :=
  if ps.isEmpty then `(True)
  else ps[0:ps.size-1].toArray.foldrM (fun t acc => `($t ∧ $acc)) ps.back!

def mkExists (ids : Array Ident) (body : Term) : CommandElabM Term :=
  ids.foldrM (fun i acc => `(∃ $i:ident, $acc)) body

/-- `_root_`-prefixed ident: unambiguous in both declaration and reference position. -/
def rootedIdent (n : Name) : Ident := mkIdent (`_root_ ++ n)

/-- Idents for generated variables (constructor fields are renamed positionally, so these
cannot clash with anything user-supplied). -/
def gid (s : String) : Ident := mkIdent (Name.mkSimple s)

/-- An rcases tuple pattern `⟨p₁, …, pₙ⟩` from sub-patterns (`⟨⟩` when empty). -/
def rcTuple (ps : Array (TSyntax `rcasesPat)) : CommandElabM (TSyntax `rcasesPat) := do
  let los : Syntax.TSepArray ``Lean.Parser.Tactic.rcasesPatLo "," :=
    .ofElems (ps.map (fun p => ((p : TSyntax ``Lean.Parser.Tactic.rcasesPatMed) : TSyntax ``Lean.Parser.Tactic.rcasesPatLo)))
  `(rcasesPat| ⟨$los,*⟩)

/-- An rcases tuple pattern `⟨i₁, …, iₙ⟩` from plain idents (an ident named `rfl` acts as the
subst pattern). A single ident collapses to the bare pattern. -/
def rcasesTuple (ids : Array Ident) : CommandElabM (TSyntax `rcasesPat) := do
  if h : ids.size = 1 then
    return (ids[0] : TSyntax `rcasesPat)
  rcTuple (ids.map fun i => (i : TSyntax `rcasesPat))

/-- A left-nested pattern `⟨⟨…⟨p₁, p₂⟩…⟩, pₙ⟩`, matching a left-associated `∧`-chain
(e.g. the result of splitting `a && b && c = true` by `Bool.and_eq_true`). -/
def rcNestLeft (ps : Array (TSyntax `rcasesPat)) : CommandElabM (TSyntax `rcasesPat) := do
  if ps.isEmpty then rcTuple #[]
  else ps[1:].toArray.foldlM (fun acc p => rcTuple #[acc, p]) ps[0]!

/-- The projection term selecting the `j`-th (0-based) component of a right-nested `k`-tuple. -/
def projComp (e : Term) (j k : Nat) : CommandElabM Term := do
  if k ≤ 1 then return e
  let mut r := e
  for _ in [0:j] do r ← `(($r).2)
  if j < k - 1 then r ← `(($r).1)
  return r

/-- A right-nested tuple term `(t₁, …, tₖ)` (`k ≥ 1`; the 1-tuple is the term itself). -/
def mkTuple (ts : Array Term) : CommandElabM Term := do
  if h : ts.size = 1 then return ts[0]
  ts[0:ts.size-1].toArray.foldrM (fun t acc => `(($t, $acc))) ts.back!

/-- A left-associated `&&`-chain `t₁ && … && tₙ`. -/
def mkAndBool (ts : Array Term) : CommandElabM Term := do
  ts[1:].toArray.foldlM (fun acc t => `($acc && $t)) ts[0]!

/-- Convert idents to `binderIdent`s (for `case` tactic argument positions). -/
def toBinderIds (ids : Array Ident) : CommandElabM (Array (TSyntax ``binderIdent)) :=
  ids.mapM fun i => `(binderIdent| $i:ident)

/-- Sequence an array of tactics. -/
def seqTac (ts : Array (TSyntax `tactic)) : CommandElabM (TSyntax `tactic) := do
  if ts.isEmpty then `(tactic| skip)
  else ts[1:].toArray.foldlM (fun acc t => `(tactic| ($acc:tactic; $t:tactic))) ts[0]!

structure FieldData where
  id : Ident
  isRec : Bool
  tyStx : Term
  deriving Inhabited

structure CtorData where
  xCtor : Ident      -- rooted ident of the datatype constructor
  fCtor : Ident      -- rooted ident of the base-functor constructor
  short : Name       -- last component of the constructor name
  injName : Name     -- full name of the auto-generated `.inj` lemma
  fields : Array FieldData
  deriving Inhabited

def CtorData.recFields (c : CtorData) : Array FieldData := c.fields.filter (·.isRec)
def CtorData.fieldIds (c : CtorData) : Array Ident := c.fields.map (·.id)
def CtorData.nonRecIds (c : CtorData) : Array Ident :=
  (c.fields.filter (!·.isRec)).map (·.id)

structure Ctx where
  xName : Name
  fName : Name
  paramIds : Array Ident
  ctors : Array CtorData

def Ctx.xRef (ctx : Ctx) : Ident := rootedIdent ctx.xName
def Ctx.name (ctx : Ctx) (s : String) : Name := ctx.xName ++ Name.mkSimple s
/-- Reference to a generated declaration: unrooted, so it also resolves against the local
recursion placeholder while the declaration itself is being elaborated. -/
def Ctx.ref (ctx : Ctx) (s : String) : Ident := mkIdent (ctx.name s)
/-- Ident used to *declare* a generated name (namespace-proof). -/
def Ctx.declId (ctx : Ctx) (s : String) : Ident := rootedIdent (ctx.name s)
def Ctx.tgenUnfoldName (ctx : Ctx) : Name :=
  (ctx.xName.updatePrefix (ctx.xName.getPrefix ++ `TGen)) ++ `unfold

def Ctx.selfTy (ctx : Ctx) : CommandElabM Term := `($(ctx.xRef) $(ctx.paramIds)*)
def Ctx.baseTy (ctx : Ctx) (carrier : Term) : CommandElabM Term :=
  `($(rootedIdent ctx.fName) $(ctx.paramIds)* $carrier)
def Ctx.paramBinders (ctx : Ctx) : CommandElabM (Array BB) := do
  if ctx.paramIds.isEmpty then return #[]
  return #[← impB ctx.paramIds (← `(Type))]

section Analysis

def analyze (xName : Name) : TermElabM Ctx := do
  let indVal ← getConstInfoInduct xName
  unless indVal.all.length == 1 do
    throwError "derive_palamedes: mutual inductives are not supported"
  unless indVal.numIndices == 0 do
    throwError "derive_palamedes: indexed inductives are not supported"
  if indVal.isNested then
    throwError "derive_palamedes: nested inductives are not supported"
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

end Analysis

section BaseFunctor

/-- Make the first `n` `∀`-binders implicit (kernel ctor types bind params explicitly;
the `inductive` frontend marks them implicit — we must do the same by hand). -/
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
      -- the same auxiliary constructions the `inductive` frontend generates (tactics like
      -- `cases`/`injection` on `XF` values need `ctorIdx`/`ctorElim`/`noConfusion`; `below`/
      -- `brecOn` are trivial for the non-recursive `XF` but harmless)
      mkRecOn fName
      mkCasesOn fName
      mkCtorIdx fName
      mkCtorElim fName
      mkNoConfusion fName
      mkBelow fName
      mkBRecOn fName
      Lean.Meta.mkInjectiveTheorems fName

end BaseFunctor

section Generators

/-- Elaborate a generated command, tracing it first. -/
def addCmd (cmd : TSyntax `command) : CommandElabM Unit := do
  trace[Palamedes.derive] "{cmd}"
  elabCommand cmd

/-- Algebra argument idents, one per constructor: `f_leaf`, `f_node`, … -/
def algIds (ctx : Ctx) : Array Ident :=
  ctx.ctors.map fun c => gid s!"f_{c.short}"

/-- The `fold` algebra argument type for one constructor: fields (recursive ↦ `β`) → `β`. -/
def algTy (c : CtorData) (β : Term) : CommandElabM Term :=
  mkArrows (c.fields.map fun f => if f.isRec then β else f.tyStx) β

def genFold (ctx : Ctx) : CommandElabM Unit := do
  let β := gid "β"
  let t := gid "t"
  let foldRef := ctx.ref "fold"
  let self ← ctx.selfTy
  let fs := algIds ctx
  let mut binders : Array BB := (← ctx.paramBinders)
  binders := binders.push (← impB #[β] (← `(Type)))
  for c in ctx.ctors, fid in fs do
    binders := binders.push (← expB fid (← algTy c (β : Term)))
  binders := binders.push (← expB t self)
  let alts ← ctx.ctors.mapIdxM fun i c => do
    let pat ← `($(c.xCtor) $(c.fieldIds)*)
    let args ← c.fields.mapM fun fd =>
      if fd.isRec then `($foldRef $fs* $(fd.id)) else pure (fd.id : Term)
    let rhs ← `($(fs[i]!) $args*)
    `(matchAltExpr| | $pat:term => $rhs:term)
  addCmd (← `(command|
    def $(ctx.declId "fold"):ident $binders:bracketedBinder* : $β :=
      match $t:ident with $alts:matchAlt*))
  -- per-constructor simp lemmas
  for hi : i in [0:ctx.ctors.size] do
    let c := ctx.ctors[i]
    let mut lb : Array BB := (← ctx.paramBinders)
    lb := lb.push (← impB #[β] (← `(Type)))
    for c' in ctx.ctors, fid' in fs do
      lb := lb.push (← impB #[fid'] (← algTy c' (β : Term)))
    for fd in c.fields do
      lb := lb.push (← impB #[fd.id] (if fd.isRec then self else fd.tyStx))
    let args ← c.fields.mapM fun fd =>
      if fd.isRec then `($foldRef $fs* $(fd.id)) else pure (fd.id : Term)
    let lemId := ctx.declId s!"fold_{c.short}"
    addCmd (← `(command|
      @[simp] theorem $lemId:ident $lb:bracketedBinder* :
          $foldRef $fs* ($(c.xCtor) $(c.fieldIds)*) = $(fs[i]!) $args* := rfl))

/-- State-threading idents, one per constructor with recursive fields: `st_node`, … -/
def stIds (ctx : Ctx) : Array (Option Ident) :=
  ctx.ctors.map fun c => if c.recFields.isEmpty then none else some (gid s!"st_{c.short}")

/-- `σ × ⋯ × σ`, `k` copies (`k ≥ 1`). -/
def stateTuple (σ : Term) : Nat → CommandElabM Term
  | 0 | 1 => pure σ
  | k + 1 => do `($σ × $(← stateTuple σ k))

/-- The `accuM` algebra type for one constructor: fields (rec ↦ `β`) → σ → m β. -/
def accuAlgTy (c : CtorData) (β σ : Term) (mId : Ident) : CommandElabM Term := do
  mkArrows (c.fields.map fun f => if f.isRec then β else f.tyStx) (← `($σ → $mId $β))

/-- The `st` argument type for one constructor: non-rec field types → σ → σᵏ. -/
def stTy (c : CtorData) (σ : Term) : CommandElabM Term := do
  mkArrows ((c.fields.filter (!·.isRec)).map (·.tyStx)) (← `($σ → $(← stateTuple σ c.recFields.size)))

/-- Build `accuM`'s right-hand side for one constructor (shared by the def and its simp lemma). -/
def accuRhs (ctx : Ctx) (c : CtorData) (ci : Nat) (allArgs : Array Term) (s : Ident) :
    CommandElabM Term := do
  let accuRef := ctx.ref "accuM"
  let fIds := algIds ctx
  let recFs := c.recFields
  if recFs.isEmpty then
    return ← `($(fIds[ci]!) $(c.fieldIds.map (fun i => (i : Term)))* $s)
  let sIds := (Array.range recFs.size).map fun j => gid s!"s{j+1}"
  let vIds := (Array.range recFs.size).map fun j => gid s!"v{j+1}"
  let mut vIdx := 0
  let mut coreArgs : Array Term := #[]
  for fd in c.fields do
    if fd.isRec then
      let v : Ident := vIds[vIdx]!
      coreArgs := coreArgs.push (v : Term)
      vIdx := vIdx + 1
    else
      coreArgs := coreArgs.push (fd.id : Term)
  let mut body ← `($(fIds[ci]!) $coreArgs* $s)
  for j in (List.range recFs.size).reverse do
    body ← `($accuRef $allArgs* $((recFs[j]!).id) $(sIds[j]!) >>= fun $(vIds[j]!) => $body)
  let stC := (stIds ctx)[ci]!.get!
  let stApp ← `($stC $(c.nonRecIds)* $s)
  if recFs.size == 1 then
    `(let $(sIds[0]!):ident := $stApp; $body)
  else
    let tup ← sIds[0:sIds.size-1].toArray.foldrM (fun i acc => `(($i, $acc))) (sIds.back! : Term)
    let alt ← `(matchAltExpr| | $tup:term => $body:term)
    let alts := #[alt]
    `(match $stApp:term with $alts:matchAlt*)

def genAccuM (ctx : Ctx) : CommandElabM Unit := do
  let β := gid "β"
  let σ := gid "σ"
  let m := gid "m"
  let t := gid "t"
  let s := gid "s"
  let accuRef := ctx.ref "accuM"
  let self ← ctx.selfTy
  let fIds := algIds ctx
  let sts := stIds ctx
  let mut binders : Array BB := #[]
  binders := binders.push (← impB #[m] (← `(Type → Type)))
  binders := binders.push (← instBn (← `(Monad $m)))
  binders := binders ++ (← ctx.paramBinders)
  binders := binders.push (← impB #[β, σ] (← `(Type)))
  let mut allArgs : Array Term := #[]
  for c in ctx.ctors, stO in sts do
    if let some stC := stO then
      binders := binders.push (← expB stC (← stTy c (σ : Term)))
      allArgs := allArgs.push (stC : Term)
  for c in ctx.ctors, fid in fIds do
    binders := binders.push (← expB fid (← accuAlgTy c (β : Term) (σ : Term) m))
  allArgs := allArgs ++ fIds.map (fun i => (i : Term))
  let alts ← ctx.ctors.mapIdxM fun i c => do
    let pat ← `($(c.xCtor) $(c.fieldIds)*)
    let rhs ← accuRhs ctx c i allArgs s
    `(matchAltExpr| | $pat:term => $rhs:term)
  addCmd (← `(command|
    def $(ctx.declId "accuM"):ident $binders:bracketedBinder* ($t : $self) ($s : $σ) : $m $β :=
      match $t:ident with $alts:matchAlt*))
  -- per-constructor simp lemmas
  for hi : i in [0:ctx.ctors.size] do
    let c := ctx.ctors[i]
    let mut lb : Array BB := #[]
    lb := lb.push (← impB #[m] (← `(Type → Type)))
    lb := lb.push (← instBn (← `(Monad $m)))
    lb := lb ++ (← ctx.paramBinders)
    lb := lb.push (← impB #[β, σ] (← `(Type)))
    for c' in ctx.ctors, stO in sts do
      if let some stC := stO then
        lb := lb.push (← impB #[stC] (← stTy c' (σ : Term)))
    for c' in ctx.ctors, fid' in fIds do
      lb := lb.push (← impB #[fid'] (← accuAlgTy c' (β : Term) (σ : Term) m))
    for fd in c.fields do
      lb := lb.push (← impB #[fd.id] (if fd.isRec then self else fd.tyStx))
    lb := lb.push (← impB #[s] (σ : Term))
    let rhs ← accuRhs ctx c i allArgs s
    let lemId := ctx.declId s!"accuM_{c.short}"
    addCmd (← `(command|
      @[simp] theorem $lemId:ident $lb:bracketedBinder* :
          $accuRef $allArgs* ($(c.xCtor) $(c.fieldIds)*) $s = $rhs := by rfl))

def genUnfoldFamily (ctx : Ctx) : CommandElabM Unit := do
  let β := gid "β"
  let G := gid "G"
  let step := gid "step"
  let b := gid "b"
  let t := gid "t"
  let f := gid "f"
  let x := gid "x"
  let d := gid "d"
  let d₀ := gid "d₀"
  let goRef := ctx.ref "unfoldGo"
  let unfoldRef := ctx.ref "unfold"
  let tgenRef := rootedIdent ctx.tgenUnfoldName
  let self ← ctx.selfTy
  let baseβ ← ctx.baseTy (β : Term)
  -- unfoldGo: the depth `d` is an argument of the recursion, not part of the seed `β`, so seed
  -- types are unchanged. Children are unfolded at `d + 1`.
  let alts ← ctx.ctors.mapM fun c => do
    let pat ← `($(c.fCtor) $(c.fieldIds)*)
    let recFs := c.recFields
    let vIds := (Array.range recFs.size).map fun j => gid s!"v{j+1}"
    let mut vIdx := 0
    let mut mkArgs : Array Term := #[]
    for fd in c.fields do
      if fd.isRec then
        let v : Ident := vIds[vIdx]!
        mkArgs := mkArgs.push (v : Term)
        vIdx := vIdx + 1
      else
        mkArgs := mkArgs.push (fd.id : Term)
    let mut rhs ← `(pure ($(c.xCtor) $mkArgs*))
    for j in (List.range recFs.size).reverse do
      rhs ← `($goRef $step ($d + 1) $((recFs[j]!).id) >>= fun $(vIds[j]!) => $rhs)
    `(matchAltExpr| | $pat:term => $rhs:term)
  let suffix ← `(Lean.Parser.Termination.suffix| partial_fixpoint)
  let mut goBinders : Array BB := #[]
  goBinders := goBinders.push (← impB #[G] (← `(Type → Type)))
  goBinders := goBinders.push (← instBn (← `(Gen $G)))
  goBinders := goBinders ++ (← ctx.paramBinders)
  goBinders := goBinders.push (← impB #[β] (← `(Type)))
  addCmd (← `(command|
    def $(ctx.declId "unfoldGo"):ident $goBinders:bracketedBinder*
        ($step : Nat → $β → $G $baseβ) ($d : Nat) ($b : $β) :
        $G $self :=
      $step $d $b >>= fun $t => match $t:ident with $alts:matchAlt*
    $suffix:suffix))
  -- unfold. The starting depth `d₀` defaults to `0`, so existing call sites are unchanged; a
  -- nested unfold can pass a nonzero one to inherit its caller's depth.
  let mut uBinders : Array BB := (← ctx.paramBinders)
  uBinders := uBinders.push (← impB #[β] (← `(Type)))
  let d₀Binder : BB := ⟨(← `(explicitBinderF| ($d₀ : Nat := 0))).raw⟩
  addCmd (← `(command|
    def $(ctx.declId "unfold"):ident $uBinders:bracketedBinder*
        ($f : Nat → $β → Palamedes.PGen $baseβ) ($b : $β) $d₀Binder:bracketedBinder :
        Palamedes.PGen $self :=
      ⟨fun {_G} _ _ => $goRef (fun $d $x => ($f $d $x).run) $d₀ $b⟩))
  -- TGen unfold
  addCmd (← `(command|
    def $tgenRef:ident $uBinders:bracketedBinder*
        ($f : Nat → $β → Palamedes.TGen $baseβ) ($b : $β) $d₀Binder:bracketedBinder :
        Palamedes.TGen $self :=
      ⟨fun {_G} _ => $goRef (fun $d $x => ($f $d $x).run) $d₀ $b⟩))
  -- run_unfold
  addCmd (← `(command|
    @[simp] theorem $(ctx.declId "run_unfold"):ident $uBinders:bracketedBinder*
        ($f : Nat → $β → Palamedes.PGen $baseβ) ($b : $β) ($d₀ : Nat)
        ($G : Type → Type) [Gen $G] [Palamedes.Fail $G] :
        ($unfoldRef $f $b $d₀).run (G := $G) = $goRef (fun $d $x => ($f $d $x).run) $d₀ $b := rfl))
  -- The `TGen` twin of `run_unfold`. Tagged `@[twitness]` rather than `@[simp]`: this is what lets
  -- the emitted generator's recursion unfold from the totality witness back to `unfoldGo`, so a
  -- synthesized generator reads as a generator rather than as a proof term. No `Fail` constraint —
  -- that is the whole point of `TGen`.
  addCmd (← `(command|
    @[twitness] theorem $(ctx.declId "trun_unfold"):ident $uBinders:bracketedBinder*
        ($f : Nat → $β → Palamedes.TGen $baseβ) ($b : $β) ($d₀ : Nat)
        ($G : Type → Type) [Gen $G] :
        ($tgenRef $f $b $d₀).run (G := $G) = $goRef (fun $d $x => ($f $d $x).run) $d₀ $b := rfl))

/-- `X.unfold_support P d b t`: the support characterization of an unfold, indexed by the depth the
step is read at. `P` is a depth-indexed step support (`fun d x => support (f d x)`), and a child at
depth `d` is characterized at `d + 1`, mirroring `unfoldGo`. -/
def genUnfoldSupport (ctx : Ctx) : CommandElabM Unit := do
  let β := gid "β"
  let P := gid "P"
  let b := gid "b"
  let t := gid "t"
  let d := gid "d"
  let usRef := ctx.ref "unfold_support"
  let self ← ctx.selfTy
  let baseβ ← ctx.baseTy (β : Term)
  let alts ← ctx.ctors.mapM fun c => do
    let pat ← `($(c.xCtor) $(c.fieldIds)*)
    let recFs := c.recFields
    if recFs.isEmpty then
      let rhs ← `($P $d $b ($(c.fCtor) $(c.fieldIds)*))
      `(matchAltExpr| | $pat:term => $rhs:term)
    else
      let bIds := (Array.range recFs.size).map fun j => gid s!"b{j+1}"
      let mut bIdx := 0
      let mut fArgs : Array Term := #[]
      for fd in c.fields do
        if fd.isRec then
          let v : Ident := bIds[bIdx]!
          fArgs := fArgs.push (v : Term)
          bIdx := bIdx + 1
        else
          fArgs := fArgs.push (fd.id : Term)
      let head ← `($P $d $b ($(c.fCtor) $fArgs*))
      let recs ← recFs.mapIdxM fun j fd => `($usRef $P ($d + 1) $(bIds[j]!) $(fd.id))
      let body ← mkAnds (#[head] ++ recs)
      let rhs ← mkExists bIds body
      `(matchAltExpr| | $pat:term => $rhs:term)
  let mut binders : Array BB := (← ctx.paramBinders)
  binders := binders.push (← impB #[β] (← `(Type)))
  addCmd (← `(command|
    @[simp] def $(ctx.declId "unfold_support"):ident $binders:bracketedBinder*
        ($P : Nat → $β → $baseβ → Prop) ($d : Nat) ($b : $β) ($t : $self) : Prop :=
      match $t:ident with $alts:matchAlt*))

/-- Which support notion `genSupportUnfold` is emitting the characterization for.

There are two: `PGen.support`, reading the generator at `SPMF` (where `Fail` is `⊥`), and
`someSupport`, reading it at `OptionT SPMF` (where `Fail` is `pure none`). The second is what a
*filtering* generator's emitted definition actually runs, so it is the one a law about `totalize g`
needs.

The two proofs are the **same script**. `X.unfoldGo` is polymorphic in `G`, so the
`unfold`/`induction` skeleton does not care which interpretation it is read at, and only the leaf
lemmas differ — which is why this is a lemma kit rather than a second emitter. The `some` on the
`OptionT` side is the whole of the difference: it appears in the membership statement, and it means
constructor injectivity has to see through an `Option.some.inj` first. -/
structure SupportKit where
  /-- Suffix of the emitted theorem: `X.support_unfold` or `X.someSupport_unfold`. -/
  thmName : String
  /-- Applied to a generator to give its support predicate. -/
  supportOf : Term → CommandElabM Term
  /-- The `bind` lemma: `SPMF.support_bind` or `mem_support_optionT_bind`. -/
  bindLem : Term
  /-- The `pure` lemma: `SPMF.support_pure` or `support_optionT_pure`. -/
  pureLem : Term
  /-- Membership-unfolding lemmas that accompany the two above in a `simp only`. -/
  memLems : Array Term
  /-- Extra lemmas in the per-case `simp only […, X.unfold_support]`. -/
  headSimp : Array Term
  /-- Wraps `w` in the membership goal: `w` at `SPMF`, `some w` at `OptionT SPMF`. -/
  memWrap : Term → CommandElabM Term
  /-- Wraps the `unfoldGo` application before `SPMF.support` is applied to it. -/
  runWrap : Term → CommandElabM Term
  /-- The `G` the `unfoldGo` application is read at, when it must be given explicitly. -/
  goInst : Option Term
  /-- Adapts an equation proof before feeding it to a constructor's injectivity lemma. On the
  `OptionT` side the equation is between `Option`s, so it needs peeling first. -/
  wrapInj : Term → CommandElabM Term

/-- The `PGen.support` kit. -/
def SupportKit.spmf : SupportKit where
  thmName := "support_unfold"
  supportOf := fun g => `(Palamedes.PGen.support $g)
  bindLem := mkIdent ``SPMF.support_bind
  pureLem := mkIdent ``SPMF.support_pure
  memLems := #[mkIdent ``Set.mem_setOf_eq, mkIdent ``Set.mem_singleton_iff]
  headSimp := #[mkIdent ``Set.mem_setOf_eq]
  memWrap := pure
  runWrap := pure
  goInst := none
  wrapInj := pure

/-- The `someSupport` kit: the same script at `OptionT SPMF`. -/
def SupportKit.optionT : SupportKit where
  thmName := "someSupport_unfold"
  supportOf := fun g => `(Palamedes.someSupport $g)
  bindLem := mkIdent ``Palamedes.mem_support_optionT_bind
  pureLem := mkIdent ``Palamedes.support_optionT_pure
  memLems := #[mkIdent ``Set.mem_singleton_iff]
  headSimp := #[]
  memWrap := fun w => `(some $w)
  runWrap := fun e => `(OptionT.run $e)
  goInst := some (Unhygienic.run `(OptionT SPMF))
  wrapInj := fun h => `(Option.some.inj $h)

/-- `X.support_unfold` / `X.someSupport_unfold` — the support characterization, by a generated
per-constructor induction.

Because `unfold_support`'s step predicate is itself depth-indexed, the characterization holds at
every depth *unconditionally*: no depth-independence hypothesis is needed, and the per-constructor
scripts below are the same ones they were before depth threading. All the statement needs is a `d₀`
binder and `generalizing d₀` on the induction. -/
def genSupportUnfold (ctx : Ctx) (kit : SupportKit) : CommandElabM Unit := do
  let β := gid "β"
  let b := gid "b"
  let f := gid "f"
  let w := gid "w"
  let x := gid "x"
  let d := gid "d"
  let d₀ := gid "d₀"
  let goRef := ctx.ref "unfoldGo"
  let usRef := ctx.ref "unfold_support"
  let baseβ ← ctx.baseTy (β : Term)
  -- The leaf lemma sets, the only place the two interpretations differ. `simpSet` is deliberately
  -- uniform across constructors — a nullary constructor's case has no `bind` to rewrite, but an
  -- unused `simp only` lemma is harmless and keeping one set makes the two kits comparable.
  let toSimpLemmas (ts : Array Term) : CommandElabM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
    ts.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  let simpSet ← toSimpLemmas (#[kit.bindLem, kit.pureLem] ++ kit.memLems)
  let pureSet ← toSimpLemmas (#[kit.pureLem] ++ kit.memLems)
  let headSet ← toSimpLemmas (kit.headSimp ++ #[(usRef : Term)])
  -- per-constructor induction cases
  let cases ← ctx.ctors.mapM fun c => do
    let recFs := c.recFields
    let ihIds := (Array.range recFs.size).map fun j => gid s!"ih{j+1}"
    let tv := gid "tv"
    let ht := gid "ht"
    let hw := gid "hw"
    -- forward direction
    let caseTacs ← ctx.ctors.mapM fun c' => do
      if c'.short != c.short then
        let tac ← `(tactic|
          simp only [$simpSet,*] at $hw:ident <;> simp_all)
        `(tactic| case $(mkIdent c'.short):ident => $tac:tactic)
      else
        let yIds := (Array.range c.fields.size).map fun j => gid s!"y{j+1}"
        let yRec := (Array.range c.fields.size).filterMap fun j =>
          if (c.fields[j]!).isRec then some (yIds[j]!) else none
        let injRef := rootedIdent c.injName
        let mut tacs : Array (TSyntax `tactic) := #[]
        if recFs.isEmpty then
          if c.fields.isEmpty then
            tacs := tacs.push (← `(tactic| exact $ht))
          else
            tacs := tacs.push (← `(tactic|
              simp only [$pureSet,*] at $hw:ident))
            let injPat ← rcasesTuple (c.fields.map fun _ => gid "rfl")
            tacs := tacs.push (← `(tactic|
              obtain $injPat:rcasesPat := $injRef $(← kit.wrapInj hw)))
            tacs := tacs.push (← `(tactic| exact $ht))
        else
          tacs := tacs.push (← `(tactic| simp only [$simpSet,*] at $hw:ident))
          let vIds := (Array.range recFs.size).map fun j => gid s!"v{j+1}"
          let hvIds := (Array.range recFs.size).map fun j => gid s!"hv{j+1}"
          let heq := gid "heq"
          let mut pats : Array Ident := #[]
          for j in [0:recFs.size] do
            pats := pats.push vIds[j]!
            pats := pats.push hvIds[j]!
          pats := pats.push heq
          tacs := tacs.push (← `(tactic| obtain $(← rcasesTuple pats):rcasesPat := $hw))
          let injPat ← rcasesTuple (c.fields.map fun _ => gid "rfl")
          tacs := tacs.push (← `(tactic|
            obtain $injPat:rcasesPat := $injRef $(← kit.wrapInj (← `(Eq.symm $heq)))))
          let mut parts : Array Term := yRec.map fun y => (y : Term)
          parts := parts.push (ht : Term)
          for j in [0:recFs.size] do
            parts := parts.push (← `(($(ihIds[j]!)).mp $(hvIds[j]!)))
          tacs := tacs.push (← `(tactic| exact ⟨$parts,*⟩))
        let tac ← seqTac tacs
        let bs ← toBinderIds yIds
        `(tactic| case $(mkIdent c.short):ident $bs:binderIdent* => $tac:tactic)
    let fwd ← seqTac (#[
      ← `(tactic| rintro $(← rcasesTuple #[tv, ht, hw]):rcasesPat),
      ← `(tactic| cases $tv:ident)] ++ caseTacs)
    -- backward direction
    let bwd ← do
      if recFs.isEmpty then
        let h := gid "h"
        let wit ← `($(c.fCtor) $(c.fieldIds)*)
        seqTac #[
          ← `(tactic| intro $h:ident),
          ← `(tactic| exact ⟨$wit, $h, by simp only [$pureSet,*]⟩)]
      else
        let bIds := (Array.range recFs.size).map fun j => gid s!"b{j+1}"
        let hb := gid "hb"
        let hIds := (Array.range recFs.size).map fun j => gid s!"h{j+1}"
        let mut pats : Array Ident := bIds
        pats := pats.push hb
        pats := pats ++ hIds
        let mut bIdx := 0
        let mut witArgs : Array Term := #[]
        for fd in c.fields do
          if fd.isRec then
            let v : Ident := bIds[bIdx]!
            witArgs := witArgs.push (v : Term)
            bIdx := bIdx + 1
          else
            witArgs := witArgs.push (fd.id : Term)
        let mut final : Array Term := #[]
        for j in [0:recFs.size] do
          let fj := recFs[j]!
          final := final.push (fj.id : Term)
          final := final.push (← `(($(ihIds[j]!)).mpr $(hIds[j]!)))
        final := final.push (← `(rfl))
        let wit ← `($(c.fCtor) $witArgs*)
        seqTac #[
          ← `(tactic| rintro $(← rcasesTuple pats):rcasesPat),
          ← `(tactic| refine ⟨$wit, $hb, ?_⟩),
          ← `(tactic| simp only [$simpSet,*]),
          ← `(tactic| exact ⟨$final,*⟩)]
    let caseTac ← seqTac #[
      ← `(tactic| unfold $goRef:ident),
      ← `(tactic| rw [$(kit.bindLem):term]),
      ← `(tactic| simp only [$headSet,*]),
      ← `(tactic| constructor),
      ← `(tactic| case mp => $fwd:tactic),
      ← `(tactic| case mpr => $bwd:tactic)]
    let bs ← toBinderIds (c.fieldIds ++ ihIds)
    `(tactic| case $(mkIdent c.short):ident $bs:binderIdent* => $caseTac:tactic)
  let proofTail ← seqTac cases
  let mut binders : Array BB := (← ctx.paramBinders)
  binders := binders.push (← impB #[β] (← `(Type)))
  binders := binders.push (← impB #[f] (← `(Nat → $β → Palamedes.PGen $baseβ)))
  binders := binders.push (← impB #[b] (β : Term))
  binders := binders.push (← impB #[d₀] (← `(Nat)))
  -- `unfoldGo` is polymorphic in `G`, so the only thing the `OptionT` reading changes here is which
  -- `G` it is instantiated at — the skeleton below is shared verbatim.
  let goApp ← match kit.goInst with
    | none => `($goRef (fun $d $x => ($f $d $x).run) $d₀ $b)
    | some inst => `($goRef (G := $inst) (fun $d $x => ($f $d $x).run) $d₀ $b)
  let lhs ← kit.supportOf (← `($(ctx.ref "unfold") $f $b $d₀))
  let step ← `(fun $d $x => $(← kit.supportOf (← `($f $d $x))))
  let memW ← kit.memWrap (w : Term)
  let runG ← kit.runWrap goApp
  addCmd (← `(command|
    @[simp] theorem $(ctx.declId kit.thmName):ident $binders:bracketedBinder* :
        $lhs = $usRef $step $d₀ $b := by
      funext $w:ident
      apply propext
      show $memW ∈ SPMF.support $runG ↔ $usRef $step $d₀ $b $w
      induction $w:ident generalizing $b:ident $d₀:ident
      $proofTail:tactic))

def genSupportUnfoldCongr (ctx : Ctx) : CommandElabM Unit := do
  let β := gid "β"
  let b := gid "b"
  let f := gid "f"
  let f' := gid "f'"
  let hf := gid "hf"
  let x := gid "x"
  let d := gid "d"
  let d₀ := gid "d₀"
  let baseβ ← ctx.baseTy (β : Term)
  let mut binders : Array BB := (← ctx.paramBinders)
  binders := binders.push (← impB #[β] (← `(Type)))
  binders := binders.push (← impB #[f, f'] (← `(Nat → $β → Palamedes.PGen $baseβ)))
  binders := binders.push (← impB #[b] (β : Term))
  binders := binders.push (← impB #[d₀] (← `(Nat)))
  addCmd (← `(command|
    @[gen_congr] theorem $(ctx.declId "support_unfold_congr"):ident $binders:bracketedBinder*
        ($hf : ∀ {$d:ident $x:ident},
          Palamedes.PGen.support ($f $d $x) = Palamedes.PGen.support ($f' $d $x)) :
        Palamedes.PGen.support ($(ctx.ref "unfold") $f $b $d₀)
          = Palamedes.PGen.support ($(ctx.ref "unfold") $f' $b $d₀) := by
      aesop))

def genTotalUnfold (ctx : Ctx) : CommandElabM Unit := do
  let β := gid "β"
  let b := gid "b"
  let g := gid "g"
  let h := gid "h"
  let x := gid "x"
  let y := gid "y"
  let d := gid "d"
  let d₀ := gid "d₀"
  let heq := gid "heq"
  let baseβ ← ctx.baseTy (β : Term)
  let mut binders : Array BB := (← ctx.paramBinders)
  binders := binders.push (← impB #[β] (← `(Type)))
  binders := binders.push (← impB #[g] (← `(Nat → $β → Palamedes.PGen $baseβ)))
  binders := binders.push (← impB #[b] (β : Term))
  binders := binders.push (← impB #[d₀] (← `(Nat)))
  addCmd (← `(command|
    @[total]
    def $(ctx.declId "total_unfold"):ident $binders:bracketedBinder*
        ($h : ∀ $d:ident $x:ident, Palamedes.PGen.total ($g $d $x)) :
        Palamedes.PGen.total ($(ctx.ref "unfold") $g $b $d₀) :=
      ⟨$(mkIdent ctx.tgenUnfoldName) (fun $d $y => ($h $d $y).val) $b $d₀, by
        have $heq:ident : (fun $d $y => (($h $d $y).val).toGen) = $g :=
          funext fun $d:ident => funext fun $y:ident => ($h $d $y).property
        conv_rhs => rw [← $heq:ident]
        ext; rfl⟩))

/-- The base functor's case-analysis totality lemma.

The synthesized step function ends in a `match` over the base functor, and `totality` has to get
past it. Doing that with `split` (or with a bare `cases`) puts a `splitter`/recursor in the witness's
**data** path, which blocks `.val` from projecting — so the emitted generator lands in the
environment as a proof term rather than as generator code. This lemma instead builds the witness
*as* a `match` producing `TGen`s, inside `TGen.mk`, so the `.run` projection cancels and what is
emitted reads exactly like a hand-written generator.

It is registered `@[total]`, so it is found through the registry like every other per-datatype fact
and `Synthesizer/Totality.lean` needs no edit. -/
def genTotalCases (ctx : Ctx) : CommandElabM Unit := do
  let β := gid "β"
  let γ := gid "γ"
  let t := gid "t"
  let baseβ ← ctx.baseTy (β : Term)
  let gs := ctx.ctors.map fun c => gid s!"g_{c.short}"
  let hs := ctx.ctors.map fun c => gid s!"h_{c.short}"
  let mut binders : Array BB := (← ctx.paramBinders)
  binders := binders.push (← impB #[β, γ] (← `(Type)))
  -- One branch generator per constructor, taking that constructor's fields.
  for c in ctx.ctors, gid' in gs do
    let fieldTys := c.fields.map fun f => if f.isRec then (β : Term) else f.tyStx
    binders := binders.push (← impB #[gid'] (← mkArrows fieldTys (← `(Palamedes.PGen $γ))))
  -- ...and a totality witness for each, universally quantified over those fields.
  for c in ctx.ctors, gid' in gs, hid in hs do
    let fieldTys := c.fields.map fun f => if f.isRec then (β : Term) else f.tyStx
    let concl ← `(Palamedes.PGen.total ($gid' $(c.fieldIds)*))
    let ty ← c.fields.zip fieldTys |>.foldrM
      (fun (fd, fty) acc => `(∀ ($(fd.id) : $fty), $acc)) concl
    binders := binders.push (← expB hid ty)
  binders := binders.push (← expB t baseβ)
  let goalAlts ← ctx.ctors.mapIdxM fun i c => do
    let pat ← `($(c.fCtor) $(c.fieldIds)*)
    `(matchAltExpr| | $pat:term => $(gs[i]!) $(c.fieldIds)*)
  let witAlts ← ctx.ctors.mapIdxM fun i c => do
    let pat ← `($(c.fCtor) $(c.fieldIds)*)
    `(matchAltExpr| | $pat:term => ($(hs[i]!) $(c.fieldIds)*).val.run)
  let proofAlts ← ctx.ctors.mapIdxM fun i c => do
    let pat ← `($(c.fCtor) $(c.fieldIds)*)
    `(matchAltExpr| | $pat:term => ($(hs[i]!) $(c.fieldIds)*).property)
  addCmd (← `(command|
    @[total]
    def $(ctx.declId "total_cases"):ident $binders:bracketedBinder* :
        Palamedes.PGen.total (match $t:ident with $goalAlts:matchAlt*) :=
      ⟨⟨fun {_G} _ => match $t:ident with $witAlts:matchAlt*⟩,
       match $t:ident with $proofAlts:matchAlt*⟩))

def genCoerceToFold (ctx : Ctx) : CommandElabM Unit := do
  let β := gid "β"
  let t := gid "t"
  let f := gid "f"
  let self ← ctx.selfTy
  let fIds := algIds ctx
  let mut binders : Array BB := (← ctx.paramBinders)
  binders := binders.push (← impB #[β] (← `(Type)))
  binders := binders.push (← impB #[t] self)
  binders := binders.push (← impB #[f] (← `($self → $β)))
  for c in ctx.ctors, fid in fIds do
    binders := binders.push (← impB #[fid] (← algTy c (β : Term)))
  for hi : i in [0:ctx.ctors.size] do
    let c := ctx.ctors[i]
    let args ← c.fields.mapM fun fd =>
      if fd.isRec then `($f $(fd.id)) else pure (fd.id : Term)
    let mut stmt ← `($f ($(c.xCtor) $(c.fieldIds)*) = $(fIds[i]!) $args*)
    for fd in c.fields.reverse do
      stmt ← `(∀ $(fd.id):ident, $stmt)
    let hId := gid s!"h_{c.short}"
    let bb ←
      if c.fields.isEmpty then
        `(explicitBinderF| ($hId : $stmt := by aesop))
      else
        `(explicitBinderF| ($hId : $stmt := by intros; simp_all; rflm))
    binders := binders.push ⟨bb.raw⟩
  -- per-constructor cases: `simp only` with exactly the constructor's hypothesis, fold
  -- equation, and induction hypotheses (a bare `simp_all` mis-handles e.g. `Bool` payload
  -- fields by splitting the ∀-hypothesis via `forall_bool`)
  let cases ← ctx.ctors.mapM fun c => do
    let recFs := c.recFields
    let ihIds := (Array.range recFs.size).map fun j => gid s!"ih{j+1}"
    let hId := gid s!"h_{c.short}"
    let lemmas : Array Term :=
      #[(hId : Term), (ctx.ref s!"fold_{c.short}" : Term)] ++ ihIds.map (fun i => (i : Term))
    let tac ← `(tactic| simp only [$[$lemmas:term],*])
    let bs ← toBinderIds (c.fieldIds ++ ihIds)
    `(tactic| case $(mkIdent c.short):ident $bs:binderIdent* => $tac:tactic)
  let proofTail ← seqTac cases
  addCmd (← `(command|
    theorem $(ctx.declId "coerce_to_fold"):ident $binders:bracketedBinder* :
        $f $t = $(ctx.ref "fold") $fIds* $t := by
      induction $t:ident
      $proofTail:tactic))

end Generators


section FusionGenerators

/-- Interleaved lambda binders for a constructor's algebra: recursive positions get fresh
`pre{j}` idents, non-recursive positions keep the (positional) field ident.
Returns (all binders in field order, the recursive-position idents). -/
def interleaved (c : CtorData) (pre : String) : Array Ident × Array Ident := Id.run do
  let mut out := #[]
  let mut recs := #[]
  let mut j := 0
  for fd in c.fields do
    if fd.isRec then
      let v := gid s!"{pre}{j+1}"
      out := out.push v
      recs := recs.push v
      j := j + 1
    else
      out := out.push fd.id
  return (out, recs)

def ihIdsFor (k : Nat) : Array Ident := (Array.range k).map fun j => gid s!"ih{j+1}"

/-- `merge_accuM` (banana split in `Option`): running two accumulating folds separately agrees
with running the pairwise-merged one. Statement and proof are constructor-indexed instances of
the hand-written `Tree.merge_accuM`. -/
def genMergeAccuM (ctx : Ctx) : CommandElabM Unit := do
  let sig1 := gid "σ1"; let sig2 := gid "σ2"; let bt1 := gid "β1"; let bt2 := gid "β2"
  let s1 := gid "s1"; let s2 := gid "s2"; let r1 := gid "r1"; let r2 := gid "r2"
  let t := gid "t"; let p := gid "p"
  let accuRef := ctx.ref "accuM"
  let self ← ctx.selfTy
  let opt := mkIdent `Option
  let st1 := ctx.ctors.map fun c =>
    if c.recFields.isEmpty then none else some (gid s!"st1_{c.short}")
  let st2 := ctx.ctors.map fun c =>
    if c.recFields.isEmpty then none else some (gid s!"st2_{c.short}")
  let fs1 := ctx.ctors.map fun c => gid s!"f1_{c.short}"
  let fs2 := ctx.ctors.map fun c => gid s!"f2_{c.short}"
  let mut binders : Array BB := (← ctx.paramBinders)
  binders := binders.push (← impB #[sig1, sig2, bt1, bt2] (← `(Type)))
  for c in ctx.ctors, o1 in st1, o2 in st2 do
    if let (some i1, some i2) := (o1, o2) then
      binders := binders.push (← impB #[i1] (← stTy c (sig1 : Term)))
      binders := binders.push (← impB #[i2] (← stTy c (sig2 : Term)))
  for c in ctx.ctors, i1 in fs1, i2 in fs2 do
    binders := binders.push (← impB #[i1] (← accuAlgTy c (bt1 : Term) (sig1 : Term) opt))
    binders := binders.push (← impB #[i2] (← accuAlgTy c (bt2 : Term) (sig2 : Term) opt))
  binders := binders.push (← impB #[s1] (sig1 : Term))
  binders := binders.push (← impB #[s2] (sig2 : Term))
  binders := binders.push (← impB #[r1] (bt1 : Term))
  binders := binders.push (← impB #[r2] (bt2 : Term))
  binders := binders.push (← impB #[t] self)
  let args1 : Array Term :=
    (st1.filterMap id).map (fun i => (i : Term)) ++ fs1.map (fun i => (i : Term))
  let args2 : Array Term :=
    (st2.filterMap id).map (fun i => (i : Term)) ++ fs2.map (fun i => (i : Term))
  -- merged arguments
  let mut mergedSts : Array Term := #[]
  let mut mergedFs : Array Term := #[]
  for hci : ci in [0:ctx.ctors.size] do
    let c := ctx.ctors[ci]
    let k := c.recFields.size
    let nr := c.nonRecIds
    if k > 0 then
      let st1c := st1[ci]!.get!
      let st2c := st2[ci]!.get!
      let app1 ← `($st1c $nr* (($p).1))
      let app2 ← `($st2c $nr* (($p).2))
      let comps ← (Array.range k).mapM fun j => do
        `(($(← projComp app1 j k), $(← projComp app2 j k)))
      let body ← mkTuple comps
      mergedSts := mergedSts.push (← `(fun $nr* $p => $body))
    let (lams, recs) := interleaved c "v"
    let mut a1 : Array Term := #[]
    let mut a2 : Array Term := #[]
    let mut vIdx := 0
    for fd in c.fields do
      if fd.isRec then
        let v := recs[vIdx]!
        a1 := a1.push (← `(($v).1))
        a2 := a2.push (← `(($v).2))
        vIdx := vIdx + 1
      else
        a1 := a1.push (fd.id : Term)
        a2 := a2.push (fd.id : Term)
    let w1 := gid "w1"; let w2 := gid "w2"
    let body ← `($(fs1[ci]!) $a1* (($p).1) >>= fun $w1 =>
      $(fs2[ci]!) $a2* (($p).2) >>= fun $w2 => pure ($w1, $w2))
    mergedFs := mergedFs.push (← `(fun $lams* $p => $body))
  let mergedArgs := mergedSts ++ mergedFs
  -- proof
  let cases ← (Array.range ctx.ctors.size).mapM fun ci => do
    let c := ctx.ctors[ci]!
    let k := c.recFields.size
    let ihs := ihIdsFor k
    let bs ← toBinderIds (c.fieldIds ++ ihs)
    if k == 0 then
      let tac ← `(tactic| simp_all [Option.bind_eq_some_iff])
      `(tactic| case $(mkIdent c.short):ident $bs:binderIdent* => $tac:tactic)
    else
      let accuLem := ctx.ref s!"accuM_{c.short}"
      let st1c := st1[ci]!.get!
      let st2c := st2[ci]!.get!
      let nr := c.nonRecIds
      let stApp1 ← `($st1c $nr* $s1)
      let stApp2 ← `($st2c $nr* $s2)
      let xs := (Array.range k).map fun j => gid s!"x{j+1}"
      let ys := (Array.range k).map fun j => gid s!"y{j+1}"
      let hxs := (Array.range k).map fun j => gid s!"hx{j+1}"
      let hys := (Array.range k).map fun j => gid s!"hy{j+1}"
      let pxs := (Array.range k).map fun j => gid s!"p{j+1}"
      let hps := (Array.range k).map fun j => gid s!"hp{j+1}"
      let H := gid "H"; let H1 := gid "H1"; let H2 := gid "H2"
      let replaces ← (Array.range k).mapM fun j => do
        let ih : Ident := ihs[j]!
        let x : Ident := xs[j]!
        let y : Ident := ys[j]!
        let pr1 ← projComp stApp1 j k
        let pr2 ← projComp stApp2 j k
        `(tactic| replace $ih:ident := @$ih $pr1 $pr2 $x $y)
      -- forward
      let mut fwdPats1 : Array Ident := #[]
      let mut fwdPats2 : Array Ident := #[]
      for j in [0:k] do
        fwdPats1 := fwdPats1 ++ #[xs[j]!, hxs[j]!]
        fwdPats2 := fwdPats2 ++ #[ys[j]!, hys[j]!]
      let fwd ← seqTac (#[
        ← `(tactic| intro $H:ident),
        ← `(tactic| obtain ⟨$H1:ident, $H2:ident⟩ := $H),
        ← `(tactic| simp only [$accuLem:term, Option.bind_eq_bind, Option.bind_eq_some_iff]
              at $H1:ident $H2:ident ⊢),
        ← `(tactic| obtain $(← rcasesTuple (fwdPats1.push H1)):rcasesPat := $H1),
        ← `(tactic| obtain $(← rcasesTuple (fwdPats2.push H2)):rcasesPat := $H2)]
        ++ replaces ++ #[← `(tactic| simp_all)])
      -- backward
      let mut bwdPats : Array Ident := #[]
      for j in [0:k] do
        bwdPats := bwdPats ++ #[pxs[j]!, hps[j]!]
      let pairSplits ← (Array.range k).mapM fun j => do
        let x : Ident := xs[j]!
        let y : Ident := ys[j]!
        let px : Ident := pxs[j]!
        `(tactic| obtain ⟨$x:ident, $y:ident⟩ := $px)
      let bwd ← seqTac (#[
        ← `(tactic| intro $H:ident),
        ← `(tactic| simp only [$accuLem:term, Option.bind_eq_bind, Option.bind_eq_some_iff]
              at $H:ident ⊢),
        ← `(tactic| obtain $(← rcasesTuple (bwdPats.push H)):rcasesPat := $H)]
        ++ pairSplits ++ replaces ++ #[← `(tactic| simp_all)])
      let tac ← seqTac #[
        ← `(tactic| apply Iff.intro),
        ← `(tactic| case mp => $fwd:tactic),
        ← `(tactic| case mpr => $bwd:tactic)]
      `(tactic| case $(mkIdent c.short):ident $bs:binderIdent* => $tac:tactic)
  let proofTail ← seqTac cases
  addCmd (← `(command|
    theorem $(ctx.declId "merge_accuM"):ident $binders:bracketedBinder* :
        ($accuRef $args1* $t $s1 = some $r1 ∧ $accuRef $args2* $t $s2 = some $r2)
          ↔ $accuRef $mergedArgs* $t ($s1, $s2) = some ($r1, $r2) := by
      induction $t:ident generalizing $s1:ident $s2:ident $r1:ident $r2:ident
      $proofTail:tactic))


/-- A `()`-tuple of size `k` (trivial state threading). -/
def unitTuple (k : Nat) : CommandElabM Term := do
  mkTuple (← (Array.range k).mapM fun _ => `(()))

/-- `fold_accu_Option_basic`: a plain fold agrees with the accumulating monadic fold whose
algebra it matches (trivial state, `Option` monad, carrier `β`). -/
def genFoldAccuBasic (ctx : Ctx) : CommandElabM Unit := do
  let β := gid "β"; let v := gid "v"; let t := gid "t"
  let foldRef := ctx.ref "fold"
  let accuRef := ctx.ref "accuM"
  let self ← ctx.selfTy
  let fIds := algIds ctx
  let mut binders : Array BB := (← ctx.paramBinders)
  binders := binders.push (← impB #[β] (← `(Type)))
  binders := binders.push (← impB #[v] (β : Term))
  binders := binders.push (← impB #[t] self)
  for c in ctx.ctors, fid in fIds do
    binders := binders.push (← impB #[fid] (← algTy c (β : Term)))
  let mut accuArgs : Array Term := #[]
  for c in ctx.ctors do
    let k := c.recFields.size
    if k > 0 then
      accuArgs := accuArgs.push (← `(fun $(c.nonRecIds)* _ => $(← unitTuple k)))
  for hci : ci in [0:ctx.ctors.size] do
    let c := ctx.ctors[ci]
    let (lams, _) := interleaved c "w"
    accuArgs := accuArgs.push (← `(fun $lams* _ => some ($(fIds[ci]!) $lams*)))
  let cases ← ctx.ctors.filterMapM fun c => do
    let k := c.recFields.size
    if k == 0 then return none
    let ihs := ihIdsFor k
    let bs ← toBinderIds (c.fieldIds ++ ihs)
    let replaces ← (Array.range k).mapM fun j => do
      let ih : Ident := ihs[j]!
      let child := (c.recFields[j]!).id
      `(tactic| replace $ih:ident := @$ih ($foldRef $fIds* $child))
    let tac ← seqTac (replaces.push (← `(tactic| simp_all)))
    return some (← `(tactic| case $(mkIdent c.short):ident $bs:binderIdent* => $tac:tactic))
  let proofTail ← seqTac cases
  addCmd (← `(command|
    theorem $(ctx.declId "fold_accu_Option_basic"):ident $binders:bracketedBinder* :
        $foldRef $fIds* $t = $v ↔ $accuRef $accuArgs* $t () = some $v := by
      induction $t:ident generalizing $v:ident <;> simp_all [Option.bind_eq_bind]
      $proofTail:tactic))

/-- The forward/backward `_true`-style proof for one constructor with `k ≥ 1` recursive fields
(shared between `fold_accu_Option_true` and `_function_true`). `foldArgs` are the extra
arguments the fold side is applied to (`#[]` or `#[i]`). -/
def trueStyleCase (c : CtorData) (foldLem accuLem hC : Term)
    (ihs : Array Ident) : CommandElabM (TSyntax `tactic) := do
  let k := c.recFields.size
  let hf := gid "hf"; let hg := gid "hg"
  let hs := (Array.range k).map fun j => gid s!"h{j+1}"
  let hvs := (Array.range k).map fun j => gid s!"hv{j+1}"
  let andEq : Term := mkCIdent ``Bool.and_eq_true
  let rwAnds : Array Term := (Array.range k).map fun _ => andEq
  -- forward
  let fwdPat ← rcNestLeft ((#[hg] ++ hs).map fun i => (i : TSyntax `rcasesPat))
  let ihRws ← (Array.range k).mapM fun j => do
    let ih : Ident := ihs[j]!
    let h : Ident := hs[j]!
    `(tactic| rw [($ih).mp $h])
  let fwd ← seqTac (#[
    ← `(tactic| intro $hf:ident),
    ← `(tactic| rw [$foldLem:term, $hC:term, $[$rwAnds:term],*] at $hf:ident),
    ← `(tactic| obtain $fwdPat:rcasesPat := $hf),
    ← `(tactic| simp only [$accuLem:term, Option.bind_eq_bind])]
    ++ ihRws ++ #[← `(tactic| simp [guard, $hg:term])])
  -- backward
  let mut bwdPats : Array (TSyntax `rcasesPat) := #[]
  for j in [0:k] do
    bwdPats := bwdPats.push (← rcTuple #[])
    bwdPats := bwdPats.push ((hvs[j]! : TSyntax `rcasesPat))
  bwdPats := bwdPats.push ((hf : TSyntax `rcasesPat))
  let mut closing : Term ← `((by simp_all))
  for j in [0:k] do
    let ih : Ident := ihs[j]!
    let hv : Ident := hvs[j]!
    closing ← `(⟨$closing, ($ih).mpr $hv⟩)
  let bwd ← seqTac #[
    ← `(tactic| intro $hf:ident),
    ← `(tactic| simp only [$accuLem:term, Option.bind_eq_bind, Option.bind_eq_some_iff]
          at $hf:ident),
    ← `(tactic| obtain $(← rcTuple bwdPats):rcasesPat := $hf),
    ← `(tactic| simp only [guard, Option.ite_none_right_eq_some] at $hf:ident),
    ← `(tactic| rw [$foldLem:term, $hC:term, $[$rwAnds:term],*]),
    ← `(tactic| exact $closing)]
  seqTac #[
    ← `(tactic| constructor),
    ← `(tactic| case mp => $fwd:tactic),
    ← `(tactic| case mpr => $bwd:tactic)]

/-- The `_true`-style proof for a constructor with no recursive fields. -/
def trueStyleBaseCase (foldLem accuLem : Term) : CommandElabM (TSyntax `tactic) := do
  let hf := gid "hf"
  let fwd ← seqTac #[
    ← `(tactic| intro $hf:ident),
    ← `(tactic| rw [$foldLem:term] at $hf:ident),
    ← `(tactic| simp [$accuLem:term, guard, $hf:term])]
  let bwd ← seqTac #[
    ← `(tactic| intro $hf:ident),
    ← `(tactic| rw [$foldLem:term]),
    ← `(tactic| simp only [$accuLem:term, guard, Option.ite_none_right_eq_some] at $hf:ident),
    ← `(tactic| simp_all)]
  seqTac #[
    ← `(tactic| constructor),
    ← `(tactic| case mp => $fwd:tactic),
    ← `(tactic| case mpr => $bwd:tactic)]

/-- `fold_accu_Option_true`: a `Bool` fold whose algebras are `g_c && acc₁ && …` agrees with the
guarded accumulating fold (trivial state). -/
def genFoldAccuTrue (ctx : Ctx) : CommandElabM Unit := do
  let t := gid "t"
  let foldRef := ctx.ref "fold"
  let accuRef := ctx.ref "accuM"
  let self ← ctx.selfTy
  let fIds := algIds ctx
  let gIds := ctx.ctors.map fun c =>
    if c.recFields.isEmpty then none else some (gid s!"g_{c.short}")
  let boolT ← `(Bool)
  let mut binders : Array BB := (← ctx.paramBinders)
  binders := binders.push (← impB #[t] self)
  for c in ctx.ctors, fid in fIds do
    binders := binders.push (← impB #[fid] (← algTy c boolT))
  for c in ctx.ctors, gO in gIds do
    if let some g := gO then
      binders := binders.push (← impB #[g]
        (← mkArrows ((c.fields.filter (!·.isRec)).map (·.tyStx)) boolT))
  -- hypotheses
  let hIds := ctx.ctors.map fun c =>
    if c.recFields.isEmpty then none else some (gid s!"h_{c.short}")
  for hci : ci in [0:ctx.ctors.size] do
    let c := ctx.ctors[ci]
    if let some h := hIds[ci]! then
      let (lams, recs) := interleaved c "acc"
      let gApp ← `($(gIds[ci]!.get!) $(c.nonRecIds)*)
      let chain ← mkAndBool (#[gApp] ++ recs.map (fun r => (r : Term)))
      let mut stmt ← `($(fIds[ci]!) $lams* = $chain)
      for l in lams.reverse do
        stmt ← `(∀ $l:ident, $stmt)
      binders := binders.push (← expB h stmt)
  -- accuM arguments
  let mut accuArgs : Array Term := #[]
  for c in ctx.ctors do
    let k := c.recFields.size
    if k > 0 then
      accuArgs := accuArgs.push (← `(fun $(c.nonRecIds)* _ => $(← unitTuple k)))
  for hci : ci in [0:ctx.ctors.size] do
    let c := ctx.ctors[ci]
    let (lams, _) := interleaved c "w"
    if c.recFields.isEmpty then
      accuArgs := accuArgs.push (← `(fun $lams* _ => guard ($(fIds[ci]!) $lams*)))
    else
      accuArgs := accuArgs.push
        (← `(fun $lams* _ => guard ($(gIds[ci]!.get!) $(c.nonRecIds)*)))
  -- proof
  let cases ← (Array.range ctx.ctors.size).mapM fun ci => do
    let c := ctx.ctors[ci]!
    let k := c.recFields.size
    let ihs := ihIdsFor k
    let bs ← toBinderIds (c.fieldIds ++ ihs)
    let foldLem : Term := ctx.ref s!"fold_{c.short}"
    let accuLem : Term := ctx.ref s!"accuM_{c.short}"
    let tac ←
      if k == 0 then trueStyleBaseCase foldLem accuLem
      else trueStyleCase c foldLem accuLem (hIds[ci]!.get! : Term) ihs
    `(tactic| case $(mkIdent c.short):ident $bs:binderIdent* => $tac:tactic)
  let proofTail ← seqTac cases
  addCmd (← `(command|
    theorem $(ctx.declId "fold_accu_Option_true"):ident $binders:bracketedBinder* :
        $foldRef $fIds* $t = true ↔ $accuRef $accuArgs* $t () = some () := by
      induction $t:ident
      $proofTail:tactic))

/-- Per-recursive-position state idents `st_c1 … st_ck` for the `_function` variants. -/
def stPosIds (ctx : Ctx) : Array (Array Ident) :=
  ctx.ctors.map fun c =>
    (Array.range c.recFields.size).map fun j => gid s!"st_{c.short}{j+1}"

/-- `fold_accu_Option_function`: a fold at function carrier `σ → β` agrees with the accumulating
monadic fold, given per-constructor conversion hypotheses. -/
def genFoldAccuFunction (ctx : Ctx) : CommandElabM Unit := do
  let β := gid "β"; let σ := gid "σ"; let i := gid "i"; let v := gid "v"; let t := gid "t"
  let sv := gid "s"; let w := gid "w"
  let foldRef := ctx.ref "fold"
  let accuRef := ctx.ref "accuM"
  let self ← ctx.selfTy
  let opt := mkIdent `Option
  let fIds := algIds ctx
  let sts := stPosIds ctx
  let gIds := ctx.ctors.map fun c =>
    if c.recFields.isEmpty then none else some (gid s!"g_{c.short}")
  let carrier ← `($σ → $β)
  let mut binders : Array BB := (← ctx.paramBinders)
  binders := binders.push (← impB #[β, σ] (← `(Type)))
  binders := binders.push (← impB #[i] (σ : Term))
  binders := binders.push (← impB #[v] (β : Term))
  binders := binders.push (← impB #[t] self)
  for c in ctx.ctors, fid in fIds do
    binders := binders.push (← impB #[fid] (← algTy c carrier))
  for hci : ci in [0:ctx.ctors.size] do
    let c := ctx.ctors[ci]
    if let some g := gIds[ci]! then
      binders := binders.push (← impB #[g] (← accuAlgTy c (β : Term) (σ : Term) opt))
      for stj in sts[ci]! do
        binders := binders.push (← impB #[stj]
          (← mkArrows ((c.fields.filter (!·.isRec)).map (·.tyStx)) (← `($σ → $σ))))
  -- hypotheses
  let hIds := ctx.ctors.map fun c =>
    if c.recFields.isEmpty then none else some (gid s!"h_{c.short}")
  for hci : ci in [0:ctx.ctors.size] do
    let c := ctx.ctors[ci]
    if let some h := hIds[ci]! then
      let (lams, recs) := interleaved c "acc"
      let mut gArgs : Array Term := #[]
      let mut rIdx := 0
      for fd in c.fields do
        if fd.isRec then
          let acc : Ident := recs[rIdx]!
          let stj : Ident := (sts[ci]!)[rIdx]!
          gArgs := gArgs.push (← `($acc ($stj $(c.nonRecIds)* $sv)))
          rIdx := rIdx + 1
        else
          gArgs := gArgs.push (fd.id : Term)
      let mut stmt ←
        `($(fIds[ci]!) $lams* $sv = $w ↔ $(gIds[ci]!.get!) $gArgs* $sv = some $w)
      stmt ← `(∀ $sv:ident $w:ident, $stmt)
      for l in lams.reverse do
        stmt ← `(∀ $l:ident, $stmt)
      binders := binders.push (← expB h stmt)
  -- accuM arguments
  let mut accuArgs : Array Term := #[]
  for hci : ci in [0:ctx.ctors.size] do
    let c := ctx.ctors[ci]
    let k := c.recFields.size
    if k > 0 then
      let comps ← (sts[ci]!).mapM fun stj => `($stj $(c.nonRecIds)* $sv)
      accuArgs := accuArgs.push (← `(fun $(c.nonRecIds)* $sv => $(← mkTuple comps)))
  for hci : ci in [0:ctx.ctors.size] do
    let c := ctx.ctors[ci]
    if c.recFields.isEmpty then
      let (lams, _) := interleaved c "w"
      accuArgs := accuArgs.push (← `(fun $lams* $sv => some ($(fIds[ci]!) $lams* $sv)))
    else
      accuArgs := accuArgs.push ((gIds[ci]!.get! : Term))
  -- proof
  let cases ← (Array.range ctx.ctors.size).mapM fun ci => do
    let c := ctx.ctors[ci]!
    let k := c.recFields.size
    let ihs := ihIdsFor k
    let bs ← toBinderIds (c.fieldIds ++ ihs)
    if k == 0 then
      let tac ← `(tactic| simp)
      `(tactic| case $(mkIdent c.short):ident $bs:binderIdent* => $tac:tactic)
    else
      let foldLem : Term := ctx.ref s!"fold_{c.short}"
      let accuLem : Term := ctx.ref s!"accuM_{c.short}"
      let hC : Term := hIds[ci]!.get!
      let hf := gid "hf"
      let vs := (Array.range k).map fun j => gid s!"v{j+1}"
      let hvs := (Array.range k).map fun j => gid s!"hv{j+1}"
      -- forward
      let mut wits : Array Term := #[]
      for j in [0:k] do
        let ih : Ident := ihs[j]!
        wits := wits.push (← `(_))
        wits := wits.push (← `(($ih).mp rfl))
      wits := wits.push (hf : Term)
      let fwd ← seqTac #[
        ← `(tactic| intro $hf:ident),
        ← `(tactic| rw [$foldLem:term, $hC:term] at $hf:ident),
        ← `(tactic| simp only [$accuLem:term, Option.bind_eq_bind, Option.bind_eq_some_iff]),
        ← `(tactic| exact ⟨$wits,*⟩)]
      -- backward
      let mut bwdPats : Array Ident := #[]
      for j in [0:k] do
        bwdPats := bwdPats ++ #[vs[j]!, hvs[j]!]
      let ihRws ← (Array.range k).mapM fun j => do
        let ih : Ident := ihs[j]!
        let hv : Ident := hvs[j]!
        `(tactic| rw [← $ih:term] at $hv:ident)
      let hvTerms : Array Term := #[foldLem, hC] ++ hvs.map (fun h => (h : Term))
      let bwd ← seqTac (#[
        ← `(tactic| intro $hf:ident),
        ← `(tactic| simp only [$accuLem:term, Option.bind_eq_bind, Option.bind_eq_some_iff]
              at $hf:ident),
        ← `(tactic| obtain $(← rcasesTuple (bwdPats.push hf)):rcasesPat := $hf)]
        ++ ihRws ++ #[
        ← `(tactic| rw [$[$hvTerms:term],*]),
        ← `(tactic| exact $hf)])
      let tac ← seqTac #[
        ← `(tactic| constructor),
        ← `(tactic| case mp => $fwd:tactic),
        ← `(tactic| case mpr => $bwd:tactic)]
      `(tactic| case $(mkIdent c.short):ident $bs:binderIdent* => $tac:tactic)
  let proofTail ← seqTac cases
  addCmd (← `(command|
    theorem $(ctx.declId "fold_accu_Option_function"):ident $binders:bracketedBinder* :
        $foldRef $fIds* $t $i = $v ↔ $accuRef $accuArgs* $t $i = some $v := by
      induction $t:ident generalizing $v:ident $i:ident
      $proofTail:tactic))

/-- `fold_accu_Option_function_true`: `σ → Bool` carrier with guarded conditions. -/
def genFoldAccuFunctionTrue (ctx : Ctx) : CommandElabM Unit := do
  let σ := gid "σ"; let i := gid "i"; let t := gid "t"; let sv := gid "s"
  let foldRef := ctx.ref "fold"
  let accuRef := ctx.ref "accuM"
  let self ← ctx.selfTy
  let fIds := algIds ctx
  let sts := stPosIds ctx
  let gIds := ctx.ctors.map fun c =>
    if c.recFields.isEmpty then none else some (gid s!"g_{c.short}")
  let carrier ← `($σ → Bool)
  let mut binders : Array BB := (← ctx.paramBinders)
  binders := binders.push (← impB #[σ] (← `(Type)))
  binders := binders.push (← impB #[i] (σ : Term))
  binders := binders.push (← impB #[t] self)
  for c in ctx.ctors, fid in fIds do
    binders := binders.push (← impB #[fid] (← algTy c carrier))
  for hci : ci in [0:ctx.ctors.size] do
    let c := ctx.ctors[ci]
    if let some g := gIds[ci]! then
      binders := binders.push (← impB #[g]
        (← mkArrows ((c.fields.filter (!·.isRec)).map (·.tyStx)) (← `($σ → Bool))))
      for stj in sts[ci]! do
        binders := binders.push (← impB #[stj]
          (← mkArrows ((c.fields.filter (!·.isRec)).map (·.tyStx)) (← `($σ → $σ))))
  -- hypotheses
  let hIds := ctx.ctors.map fun c =>
    if c.recFields.isEmpty then none else some (gid s!"h_{c.short}")
  for hci : ci in [0:ctx.ctors.size] do
    let c := ctx.ctors[ci]
    if let some h := hIds[ci]! then
      let (lams, recs) := interleaved c "acc"
      let gApp ← `($(gIds[ci]!.get!) $(c.nonRecIds)* $sv)
      let mut accApps : Array Term := #[]
      for hj : j in [0:recs.size] do
        let acc : Ident := recs[j]!
        let stj : Ident := (sts[ci]!)[j]!
        accApps := accApps.push (← `($acc ($stj $(c.nonRecIds)* $sv)))
      let chain ← mkAndBool (#[gApp] ++ accApps)
      let mut stmt ← `($(fIds[ci]!) $lams* $sv = $chain)
      stmt ← `(∀ $sv:ident, $stmt)
      for l in lams.reverse do
        stmt ← `(∀ $l:ident, $stmt)
      binders := binders.push (← expB h stmt)
  -- accuM arguments
  let mut accuArgs : Array Term := #[]
  for hci : ci in [0:ctx.ctors.size] do
    let c := ctx.ctors[ci]
    let k := c.recFields.size
    if k > 0 then
      let comps ← (sts[ci]!).mapM fun stj => `($stj $(c.nonRecIds)* $sv)
      accuArgs := accuArgs.push (← `(fun $(c.nonRecIds)* $sv => $(← mkTuple comps)))
  for hci : ci in [0:ctx.ctors.size] do
    let c := ctx.ctors[ci]
    let (lams, _) := interleaved c "w"
    if c.recFields.isEmpty then
      accuArgs := accuArgs.push (← `(fun $lams* $sv => guard ($(fIds[ci]!) $lams* $sv)))
    else
      accuArgs := accuArgs.push
        (← `(fun $lams* $sv => guard ($(gIds[ci]!.get!) $(c.nonRecIds)* $sv)))
  -- proof
  let cases ← (Array.range ctx.ctors.size).mapM fun ci => do
    let c := ctx.ctors[ci]!
    let k := c.recFields.size
    let ihs := ihIdsFor k
    let bs ← toBinderIds (c.fieldIds ++ ihs)
    let foldLem : Term := ctx.ref s!"fold_{c.short}"
    let accuLem : Term := ctx.ref s!"accuM_{c.short}"
    let tac ←
      if k == 0 then trueStyleBaseCase foldLem accuLem
      else trueStyleCase c foldLem accuLem (hIds[ci]!.get! : Term) ihs
    `(tactic| case $(mkIdent c.short):ident $bs:binderIdent* => $tac:tactic)
  let proofTail ← seqTac cases
  addCmd (← `(command|
    theorem $(ctx.declId "fold_accu_Option_function_true"):ident $binders:bracketedBinder* :
        $foldRef $fIds* $t $i = true ↔ $accuRef $accuArgs* $t $i = some () := by
      induction $t:ident generalizing $i:ident
      $proofTail:tactic))

/-- `s_unfold` (+ its `@[extract]` `_val` lemma): the `CorrectGen` combinator that runs the
generated `unfold` against a per-step correct generator, certified against `accuM`. The step
predicate, seed threading, and proof are constructor-indexed instances of the hand-written
`List.s_unfold`/`Tree.s_unfold`. -/
def genSUnfold (ctx : Ctx) : CommandElabM Unit := do
  let β := gid "β"; let σ := gid "σ"; let s := gid "s"; let b := gid "b"
  let g := gid "g"; let bg := gid "bg"; let sg := gid "sg"
  let tv := gid "tv"; let p := gid "p"; let v := gid "v"; let h := gid "h"
  let dv := gid "d"
  let accuRef := ctx.ref "accuM"
  let unfoldRef := ctx.ref "unfold"
  let opt := mkIdent `Option
  let sts := stIds ctx
  let fIds := algIds ctx
  -- binders (shared by s_unfold and s_unfold_val)
  let mut binders : Array BB := (← ctx.paramBinders)
  binders := binders.push (← impB #[β, σ] (← `(Type)))
  for c in ctx.ctors, stO in sts do
    if let some stC := stO then
      binders := binders.push (← impB #[stC] (← stTy c (σ : Term)))
  for c in ctx.ctors, fid in fIds do
    binders := binders.push (← impB #[fid] (← accuAlgTy c (β : Term) (σ : Term) opt))
  binders := binders.push (← impB #[s] (σ : Term))
  binders := binders.push (← impB #[b] (β : Term))
  -- The step predicate: one existential disjunct per constructor, quantified non-recursive
  -- fields first, then recursive seeds (declaration order within each group). This is the
  -- synthesizer's input contract, not a heuristic of this generator: every hand-written
  -- `s_unfold` used exactly this order (it is field order for `List`/`Stack`/`Term`, and the
  -- hand `Tree.s_unfold` deliberately deviated from field order to it — `∃ a bl br`).
  -- `normalize_and_apply`'s `s_bind` decomposition commits to one `∃`-splitting per goal, so
  -- the order the statement fixes is the order the search explores; emitting a different one
  -- means re-tuning the search, not just the inputs.
  let disjuncts ← (Array.range ctx.ctors.size).mapM fun ci => do
    let c := ctx.ctors[ci]!
    let fC : Ident := fIds[ci]!
    let inner ← `($fC $(c.fieldIds)* $sg = some $bg ∧ $tv = $(c.fCtor) $(c.fieldIds)*)
    mkExists (c.nonRecIds ++ c.recFields.map (·.id)) inner
  let disj ← disjuncts[0:disjuncts.size-1].toArray.foldrM (fun d acc => `($d ∨ $acc)) disjuncts.back!
  let baseβ ← ctx.baseTy (β : Term)
  let gTy ← `(($bg : $β) → ($sg : $σ) → Palamedes.CorrectGen fun ($tv : $baseβ) => $disj)
  binders := binders.push (← expB g gTy)
  -- the step generator
  let alts ← (Array.range ctx.ctors.size).mapM fun ci => do
    let c := ctx.ctors[ci]!
    let k := c.recFields.size
    let pat ← `($(c.fCtor) $(c.fieldIds)*)
    let rhs ←
      if k == 0 then
        `(pure ($(c.fCtor) $(c.fieldIds)*))
      else do
        let stC : Ident := sts[ci]!.get!
        let stApp ← `($stC $(c.nonRecIds)* (($p).2))
        let mut mix : Array Term := #[]
        let mut j := 0
        for fd in c.fields do
          if fd.isRec then
            mix := mix.push (← `(($(fd.id), $(← projComp stApp j k))))
            j := j + 1
          else
            mix := mix.push (fd.id : Term)
        `(pure ($(c.fCtor) $mix*))
    `(matchAltExpr| | $pat:term => $rhs:term)
  -- The synthesized step ignores the depth — nothing the search produces is depth-dependent — but
  -- the binder must be here, and must be binder 0, for the optimizer's `installTuning` pass to
  -- find a depth to schedule this step's weights against. It is named `d` rather than `_d` even
  -- though it starts out unused: `installTuning` puts it in the weights of the very generators
  -- one reads, and a binder that renames itself depending on a later pass is worse than one that
  -- is occasionally unused.
  let stepLam ← `(fun $dv $p => ($g (($p).1) (($p).2)).val >>= fun $tv =>
    match $tv:ident with $alts:matchAlt*)
  let stfArgs : Array Term :=
    (sts.filterMap id).map (fun i => (i : Term)) ++ fIds.map (fun i => (i : Term))
  -- the correctness proof
  let cases ← (Array.range ctx.ctors.size).mapM fun ci => do
    let c := ctx.ctors[ci]!
    let k := c.recFields.size
    let ihs := ihIdsFor k
    let bs ← toBinderIds (c.fieldIds ++ ihs)
    let htv := gid "htv"
    let propTac ← `(tactic|
      cases $tv:ident <;> simp_all [($g $b $s).property, -Bool.exists_bool])
    let mp ←
      if k == 0 then
        seqTac #[
          ← `(tactic| intro $h:ident),
          ← `(tactic| obtain ⟨$tv:ident, $htv:ident, $h:ident⟩ := $h),
          propTac]
      else do
        let mut pats : Array (TSyntax `rcasesPat) := #[]
        for j in [0:k] do
          pats := pats.push ((gid s!"b{j+1}" : TSyntax `rcasesPat))
          pats := pats.push ((gid s!"s{j+1}" : TSyntax `rcasesPat))
        pats := pats.push (← rcTuple #[(tv : TSyntax `rcasesPat),
          (htv : TSyntax `rcasesPat), (h : TSyntax `rcasesPat)])
        for j in [0:k] do
          pats := pats.push ((gid s!"h{j+1}" : TSyntax `rcasesPat))
        seqTac #[
          ← `(tactic| intro $h:ident),
          ← `(tactic| obtain $(← rcTuple pats):rcasesPat := $h),
          propTac]
    let mpr ←
      if k == 0 then do
        let wit ← `($(c.fCtor) $(c.fieldIds)*)
        seqTac #[
          ← `(tactic| intro $h:ident),
          ← `(tactic| exact ⟨$wit, by simp_all [($g $b $s).property, -Bool.exists_bool]⟩)]
      else do
        let accuLem : Term := ctx.ref s!"accuM_{c.short}"
        let stC : Ident := sts[ci]!.get!
        let stApp ← `($stC $(c.nonRecIds)* $s)
        let seedIds := (Array.range k).map fun j => gid s!"b{j+1}"
        let hIds := (Array.range k).map fun j => gid s!"h{j+1}"
        let mut obtPats : Array Ident := #[]
        for j in [0:k] do
          obtPats := obtPats ++ #[seedIds[j]!, hIds[j]!]
        -- the base-functor witness over the seeds
        let mut fArgs : Array Term := #[]
        let mut ri := 0
        for fd in c.fields do
          if fd.isRec then
            let sid : Ident := seedIds[ri]!
            fArgs := fArgs.push (sid : Term)
            ri := ri + 1
          else
            fArgs := fArgs.push (fd.id : Term)
        let fWit ← `($(c.fCtor) $fArgs*)
        let mut parts : Array Term := #[]
        for j in [0:k] do
          let sid : Ident := seedIds[j]!
          parts := parts.push (sid : Term)
          parts := parts.push (← projComp stApp j k)
        parts := parts.push
          (← `(⟨$fWit, by simp_all [($g $b $s).property, -Bool.exists_bool]⟩))
        for _ in [0:k] do
          parts := parts.push (← `((by simp_all)))
        seqTac #[
          ← `(tactic| intro $h:ident),
          ← `(tactic| simp only [$accuLem:term, Option.bind_eq_bind, Option.bind_eq_some_iff]
                at $h:ident),
          ← `(tactic| obtain $(← rcasesTuple (obtPats.push h)):rcasesPat := $h),
          ← `(tactic| exact ⟨$parts,*⟩)]
    let tac ← seqTac #[
      ← `(tactic| apply Iff.intro),
      ← `(tactic| case mp => $mp:tactic),
      ← `(tactic| case mpr => $mpr:tactic)]
    `(tactic| case $(mkIdent c.short):ident $bs:binderIdent* => $tac:tactic)
  let proofTail ← seqTac cases
  addCmd (← `(command|
    def $(ctx.declId "s_unfold"):ident $binders:bracketedBinder* :
        Palamedes.CorrectGen (fun $v => $accuRef $stfArgs* $v $s = some $b) :=
      Subtype.mk ($unfoldRef $stepLam ($b, $s)) <| by
        rw [$(ctx.ref "support_unfold"):term]
        -- the unfold starts at depth `0` but characterizes a child at `d + 1`, so the induction
        -- has to run at an arbitrary depth
        generalize (0 : Nat) = $dv
        funext $v:ident
        induction $v:ident generalizing $b:ident $s:ident $dv:ident <;>
          simp_all [-Bool.exists_bool]
        $proofTail:tactic))
  -- the @[extract] value lemma
  let mut sArgs : Array Term := #[]
  for _ in ctx.paramIds do
    sArgs := sArgs.push (← `(_))
  sArgs := sArgs.push (← `(_))  -- β
  sArgs := sArgs.push (← `(_))  -- σ
  sArgs := sArgs ++ stfArgs
  sArgs := sArgs.push (s : Term)
  sArgs := sArgs.push (b : Term)
  sArgs := sArgs.push (g : Term)
  addCmd (← `(command|
    @[extract] theorem $(ctx.declId "s_unfold_val"):ident $binders:bracketedBinder* :
        (@$(ctx.ref "s_unfold") $sArgs*).val = $unfoldRef $stepLam ($b, $s) := rfl))

end FusionGenerators

syntax (name := derivePalamedes) "derive_palamedes " ident : command

@[command_elab derivePalamedes]
def elabDerivePalamedes : CommandElab := fun stx => do
  let xName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let ctx ← liftTermElabM do
    let ctx ← analyze xName
    genBaseFunctor xName ctx.fName
    pure ctx
  genFold ctx
  genAccuM ctx
  genUnfoldFamily ctx
  genUnfoldSupport ctx
  genSupportUnfold ctx SupportKit.spmf
  genSupportUnfold ctx SupportKit.optionT
  genSupportUnfoldCongr ctx
  genTotalUnfold ctx
  genTotalCases ctx
  genCoerceToFold ctx
  genMergeAccuM ctx
  genFoldAccuBasic ctx
  genFoldAccuTrue ctx
  genFoldAccuFunction ctx
  genFoldAccuFunctionTrue ctx
  genSUnfold ctx
  -- register the type with the synthesizer: `normalize_and_apply_unfold` reads this entry, so the
  -- derived type participates in unfold synthesis with no synthesizer edits. (Totality goes through
  -- the sibling registry — `total_unfold` is emitted with an `@[total]` tag above.)
  liftCoreM <| Palamedes.registerUnfoldStrategy {
    typeName := ctx.xName
    sUnfold := ctx.name "s_unfold"
    fold := ctx.name "fold"
    coerce := ctx.name "coerce_to_fold"
    merge := ctx.name "merge_accuM"
    convert := #[ctx.name "fold_accu_Option_true", ctx.name "fold_accu_Option_function",
                 ctx.name "fold_accu_Option_function_true", ctx.name "fold_accu_Option_basic"]
    unfoldName := ctx.name "unfold"
  }

end Palamedes.Derive
