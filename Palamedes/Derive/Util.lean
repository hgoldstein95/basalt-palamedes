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
# Helpers for `derive_palamedes`

Quotation-level constructors (binders, tuples, rcases patterns, tactic sequencing), the `Ctx` record
describing the datatype being derived, and the argument-shape helpers (`algIds`, `algTy`, `stIds`,
`accuAlgTy`, `stTy`) that the `fold`/`accuM` families and the fusion lemmas both build from.
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

/-- Split an `↔` goal and discharge the two halves. -/
def mkIffSplit (fwd bwd : TSyntax `tactic) : CommandElabM (TSyntax `tactic) := do
  seqTac #[
    ← `(tactic| constructor),
    ← `(tactic| case mp => $fwd:tactic),
    ← `(tactic| case mpr => $bwd:tactic)]

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

/-- Interleaved binders for a constructor's fields: recursive positions get fresh `pre{j}` idents,
non-recursive positions keep the (positional) field ident.
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

/-- Induction-hypothesis idents `ih1 … ihk`, in the order `induction` binds them. -/
def ihIdsFor (k : Nat) : Array Ident := (Array.range k).map fun j => gid s!"ih{j+1}"

/-- `#[a₁, b₁, …, aₖ, bₖ]` — the order a witness/hypothesis chain `∃ x, h ∧ …` is destructured and
rebuilt in. Stops at the shorter array. -/
def interleavePairs {α : Type} (as bs : Array α) : Array α := Id.run do
  let mut out := #[]
  for a in as, b in bs do
    out := out.push a
    out := out.push b
  return out

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

/-- Implicit binders for one constructor's fields, recursive positions taken at the datatype
itself. This is how a per-constructor simp lemma re-binds what the definition matched on. -/
def ctorBinders (c : CtorData) (self : Term) : CommandElabM (Array BB) :=
  c.fields.mapM fun fd => impB #[fd.id] (if fd.isRec then self else fd.tyStx)

/-- The binders `X.fold` and its per-constructor simp lemmas share: parameters, the carrier, and
one algebra argument per constructor — explicit in the definition, implicit in the lemmas. -/
def foldBinders (ctx : Ctx) (β : Ident) (explicit : Bool) : CommandElabM (Array BB) := do
  let mut bs : Array BB := (← ctx.paramBinders)
  bs := bs.push (← impB #[β] (← `(Type)))
  for c in ctx.ctors, fid in algIds ctx do
    let ty ← algTy c (β : Term)
    bs := bs.push (← if explicit then expB fid ty else impB #[fid] ty)
  return bs

/-- The binders `X.accuM` and its per-constructor simp lemmas share: the monad, the parameters, the
carrier and state, one state-threading argument per recursive constructor, and one algebra argument
per constructor — explicit in the definition, implicit in the lemmas. -/
def accuBinders (ctx : Ctx) (β σ m : Ident) (explicit : Bool) : CommandElabM (Array BB) := do
  let mut bs : Array BB := #[← impB #[m] (← `(Type → Type)), ← instBn (← `(Monad $m))]
  bs := bs ++ (← ctx.paramBinders)
  bs := bs.push (← impB #[β, σ] (← `(Type)))
  for c in ctx.ctors, stO in stIds ctx do
    if let some stC := stO then
      let ty ← stTy c (σ : Term)
      bs := bs.push (← if explicit then expB stC ty else impB #[stC] ty)
  for c in ctx.ctors, fid in algIds ctx do
    let ty ← accuAlgTy c (β : Term) (σ : Term) m
    bs := bs.push (← if explicit then expB fid ty else impB #[fid] ty)
  return bs

/-- The arguments `X.accuM` is applied to at a use site, in binder order: state-threading first,
then algebras. -/
def accuArgIds (ctx : Ctx) : Array Term :=
  ((stIds ctx).filterMap id).map (fun i => (i : Term)) ++ (algIds ctx).map (fun i => (i : Term))

end Palamedes.Derive
