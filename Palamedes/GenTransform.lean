/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.PGen
import Palamedes.Support
import Palamedes.OptimizeCongr
import Palamedes.UnfoldStrategy

/-!
# Generator transformation substrate

A proof-maintaining rewrite over a raw `PGen`: `transform` descends the combinator spine, applies a
`HeadRewrite` at each node, and threads a `support`-preservation proof through the `@[gen_congr]`
table, so the result carries `support input = support output`. The driver is pass-agnostic; each
client supplies its own pass:

- `Palamedes.Optimizer` — the optimizing passes (`mainPass`, `flattenPass`) and `optimizeGen`.
- `Palamedes.Tuning` — `installTuning`, which reweights each `oneOf` to read a runtime `Tuning`.
-/

open Lean Elab Command Term Meta

namespace Palamedes

open Palamedes.PGen

/-- Elements of a literal `List` (`a :: … :: []`), or `none` if any spine node is not `cons`/`nil`. -/
partial def listLitElems? (e : Expr) : Option (List Expr) :=
  match e.getAppFnArgs with
  | (``List.cons, #[_, h, t]) => (h :: ·) <$> listLitElems? t
  | (``List.nil, #[_]) => some []
  | _ => none

/-- Per-constructor recursive-field counts for a base functor (e.g., `ListF`). -/
def baseCtorHoles (fName : Name) : MetaM (Std.HashMap Name Nat) := do
  let iv ← getConstInfoInduct fName
  let mut m : Std.HashMap Name Nat := {}
  for cn in iv.ctors do
    let ci ← getConstInfoCtor cn
    let n ← forallBoundedTelescope ci.type iv.numParams fun params body => do
      let some carrier := params.back? | return 0
      forallTelescope body fun fields _ =>
        fields.foldlM (init := 0) fun acc f => do
          return if (← inferType f) == carrier then acc + 1 else acc
    m := m.insert cn n
  return m

/-- Counts how many recursive children one branch of a step generator produces. -/
partial def branchHoles (holes : Std.HashMap Name Nat) (e : Expr) : MetaM Nat := do
  let underBinder (f : Expr) : MetaM Nat := do
    forallBoundedTelescope (← inferType f) (some 1) fun xs _ => do
      let #[x] := xs | return 0
      branchHoles holes (f.beta #[x])
  match_expr ← withReducible (reduce e) with
  | pure _ _ _ a =>
    let some c := a.getAppFn.constName? | return 0
    return holes.getD c 0
  | bind _ _ _ _ _ f => underBinder f
  | assume _ _ f => underBinder f
  | dite _ _ _ t f => return max (← underBinder t) (← underBinder f)
  | ite _ _ _ t f => return max (← branchHoles holes t) (← branchHoles holes f)
  | PGen.pick _ x y => return max (← branchHoles holes x) (← branchHoles holes y)
  | PGen.oneOf _ gs _ =>
    let some elems := listLitElems? gs | return 0
    elems.foldlM (init := 0) fun acc g => return max acc (← branchHoles holes g)
  | PGen.frequency _ gs _ =>
    -- Children are rewritten before the head, so an inner choice is already a `frequency` here.
    -- Scoring it 0 (omitting this case) is unsafe: a decay policy grows a 0-hole branch's weight
    -- fastest.
    let some elems := listLitElems? gs | return 0
    elems.foldlM (init := 0) fun acc p => do
      match p.getAppFnArgs with
      | (``Prod.mk, #[_, _, _, g]) => return max acc (← branchHoles holes g)
      | _ => return acc
  | _ => return 0

/-! ## Proof helpers -/

/-- `support e`. -/
def mkSupport (e : Expr) : MetaM Expr := mkAppM ``PGen.support #[e]

/-- `rfl : support e = support e`. -/
def mkSupportRefl (e : Expr) : MetaM Expr := do mkEqRefl (← mkSupport e)

/-- `fun xs => rfl` for an unchanged binder `f` whose codomain is a `PGen`. -/
private def mkBinderRefl (f : Expr) : MetaM Expr := do
  forallTelescope (← inferType f) fun xs _ => do
    mkLambdaFVars xs (← mkSupportRefl (f.beta xs))

/-- Reject a proof that still mentions a metavariable, expression or universe.

Such a proof type-checks here and survives into `synthesisExt`, where `@[correct]` reads it back in a
fresh `MetaM`: the metavariable context is gone, and the only symptom is `unknown universe
metavariable` reported against the declaration, two stages away and with no `?m` visible in it. -/
private def ensureNoMVars (lemmaName : Name) (pf : Expr) : MetaM Expr := do
  let pf ← instantiateMVars pf
  if pf.hasMVar || pf.hasLevelMVar then
    throwError "transform: the proof built from `{lemmaName}` has an unassigned metavariable\
      {indentExpr pf}"
  return pf

/-- Prove `support lhs = support rhs` via twin lemma `lemmaName`, in whichever orientation it is
stated. -/
def mkLeafProof (lemmaName : Name) (lhs rhs : Expr) : MetaM Expr := do
  let lhsS ← mkSupport lhs
  let rhsS ← mkSupport rhs
  -- Fresh instance per attempt, so a failed `isDefEq` cannot pollute the next.
  let tryOrient (a b : Expr) : MetaM (Option Expr) := do
    let lem ← mkConstWithFreshMVarLevels lemmaName
    let (mvars, _, concl) ← forallMetaTelescope (← inferType lem)
    if ← isDefEq concl (← mkEq a b) then return some (← instantiateMVars (mkAppN lem mvars))
    else return none
  if let some pf ← tryOrient lhsS rhsS then return ← ensureNoMVars lemmaName pf
  if let some pf ← tryOrient rhsS lhsS then return ← ensureNoMVars lemmaName (← mkEqSymm pf)
  throwError "transform: twin lemma `{lemmaName}` matches neither orientation of goal\
    {indentExpr (← mkEq lhsS rhsS)}"

/-- Discharge the congruence hypotheses of `lemmaName` with the child proofs `hyps`, proving
`support node = support node'`.

The lemma's structural arguments unify from the goal; the leftover binders are the hypotheses,
matched to `hyps` by type so hypothesis order need not track argument order (tolerating implicit and
interleaved hypotheses, e.g. `support_caseTy_congr`). -/
private def mkCongrProof (lemmaName : Name) (node node' : Expr) (hyps : Array Expr) : MetaM Expr := do
  let goal ← mkEq (← mkSupport node) (← mkSupport node')
  let lem ← mkConstWithFreshMVarLevels lemmaName
  let (mvars, _, concl) ← forallMetaTelescope (← inferType lem)
  unless ← isDefEq concl goal do
    throwError "transform: congruence lemma `{lemmaName}` does not match goal{indentExpr goal}"
  let mut hypMvars := #[]
  for m in mvars do
    unless ← m.mvarId!.isAssigned do
      hypMvars := hypMvars.push m
  unless hypMvars.size == hyps.size do
    throwError "transform: `{lemmaName}` expects {hypMvars.size} hypotheses, given {hyps.size}"
  let mut pool := hyps.toList
  for m in hypMvars do
    let mut rest : List Expr := []
    let mut matched := false
    for h in pool do
      if !matched && (← isDefEq m h) then
        matched := true
      else
        rest := rest ++ [h]
    unless matched do
      throwError "transform: no child proof discharges a hypothesis of `{lemmaName}`"
    pool := rest
  ensureNoMVars lemmaName (mkAppN lem mvars)

/-- A transformed subterm: the rewritten `expr` and, when it changed, a proof `support input =
support expr` (`none` = unchanged, i.e. `rfl`). -/
structure TransformResult where
  expr : Expr
  proof? : Option Expr

/-- Compose optional `support`-equality proofs with `Eq.trans`, dropping `rfl` (`none`) links; the
shared midpoints are defeq, so it type-checks across the gaps. -/
def chainProofs (ps : Array (Option Expr)) : MetaM (Option Expr) :=
  ps.foldlM (init := none) fun acc p =>
    match acc, p with
    | none, x => pure x
    | some a, none => pure (some a)
    | some a, some b => some <$> mkEqTrans a b

/-- Determines if `e` contains a `PGen` — directly, under binders, or in a `List`/`Prod`. -/
private partial def isGenValued (e : Expr) : MetaM Bool := do
  forallTelescopeReducing (← inferType e) fun _ body => go body
where
  go (ty : Expr) : MetaM Bool := do
    match ty.getAppFn.constName? with
    | some ``PGen => return true
    | some ``List => return (← ty.getAppArgs[0]?.mapM go).getD false
    | some ``Prod => ty.getAppArgs.anyM go
    | _ => return false

/-- The depth binder currently in scope, with the datatype whose recursion introduced it. A nested
unfold rebinds it — innermost wins. -/
abbrev Depth := Option (Expr × Name)

/-- A rewrite policy for already-reduced head-terms. It has the following contract:
- The function may assume that `e` is already fully reduced.
- The function must ensure that either:
  - its result is `none`; or
  - its result is `some (e', p)` where `p` proves that `support e = support e'`. -/
abbrev HeadRewrite := (d : Depth) → (e : Expr) → MetaM (Option (Expr × Expr))

/-! ## Proof-carrying traversal -/

/-- The traversal's single notion of "already reduced": reduction at `reducible` transparency. -/
private def reduceExpr (e : Expr) : MetaM Expr := withReducible (reduce e)

mutual

/-- Transform an already-reduced `e`: rewrite its children, attempt one head rewrite, then re-reduce
and re-transform the result (a rewrite can expose new redexes).

Reducing only here and at the entry avoids re-reducing each subtree once per level. -/
private partial def transformReduced (pass : HeadRewrite) (table : Array CongrRule) (depth : Depth)
    (e : Expr) : MetaM TransformResult := do
  let cong ← transformChildren pass table depth e
  match ← pass depth cong.expr with
  | none => return cong
  | some (e', headPf) =>
    let rest ← transformReduced pass table depth (← reduceExpr e')
    let proof? ← chainProofs #[cong.proof?, some headPf, rest.proof?]
    return { expr := rest.expr, proof? }

/-- Descend into a `oneOf`'s branches.

It cannot be registered through the `@[gen_congr]` table, since `h : gs ≠ []` is dependent on the
branch list, so a new list with the old proof is ill-typed. Without this hand-written descent,
`installTuning` could not reach a choice nested under another choice. -/
private partial def transformOneOfChildren?
    (pass : HeadRewrite) (table : Array CongrRule) (depth : Depth)
    (e : Expr) : MetaM (Option TransformResult) := do
  let_expr PGen.oneOf α gs h := e | return none
  -- Every branch list is a `mkListLit`; a non-literal one is a bug, not a shape to skip silently.
  let some elems := listLitElems? gs
    | throwError "transform: `oneOf` with a non-literal branch list; cannot descend into\
        {indentExpr gs}"
  if elems.isEmpty then return none
  let rs ← elems.mapM (transformReduced pass table depth)
  unless rs.any (·.proof?.isSome) do return none
  let elems' := rs.map (·.expr)
  let genα ← mkAppM ``PGen #[α]
  let gs' ← mkListLit genα elems'
  let h' ← mkAppOptM ``List.cons_ne_nil #[genα, elems'.head!, ← mkListLit genα elems'.tail!]
  -- `gs.map support = gs'.map support`, folded from the per-branch proofs; both lists reduce, so it
  -- type-checks against the `map` form by defeq.
  let propTy ← mkArrow α (mkSort .zero)
  let consFn := mkAppN (mkConst ``List.cons [Level.zero]) #[propTy]
  let mut hgMap ← mkEqRefl (← mkListLit propTy [])
  for (g, r) in (elems.zip rs).reverse do
    let pg ← match r.proof? with
      | some p => pure p
      | none   => mkEqRefl (← mkSupport g)
    hgMap ← mkCongr (← mkCongrArg consFn pg) hgMap
  let hg ← mkExpectedTypeHint hgMap
    (← mkEq (← mkAppM ``List.map #[← mkAppOptM ``PGen.support #[α], gs])
            (← mkAppM ``List.map #[← mkAppOptM ``PGen.support #[α], gs']))
  let e' ← mkAppOptM ``PGen.oneOf #[α, gs', h']
  let proof ← mkAppOptM ``support_oneOf_congr #[α, gs, gs', hg, h, h']
  return some { expr := e', proof? := some proof }

/-- The `frequency` counterpart of `transformOneOfChildren?`, exempt from the table for the same
reason: `h : 0 < (gs.map Prod.fst).sum` is dependent on the branch list. -/
private partial def transformFrequencyChildren? (pass : HeadRewrite) (table : Array CongrRule)
    (depth : Depth) (e : Expr) : MetaM (Option TransformResult) := do
  let_expr PGen.frequency α gs h := e | return none
  let some elems := listLitElems? gs
    | throwError "transform: `frequency` with a non-literal branch list; cannot descend into\
        {indentExpr gs}"
  if elems.isEmpty then return none
  let pairs ← elems.mapM fun p =>
    match p.getAppFnArgs with
    | (``Prod.mk, #[_, _, w, g]) => pure (w, g)
    | _ => throwError "transform: `frequency` branch is not a literal (weight, generator) pair; \
        cannot descend into{indentExpr p}"
  let rs ← pairs.mapM fun (_, g) => transformReduced pass table depth g
  unless rs.any (·.proof?.isSome) do return none
  let genα ← mkAppM ``PGen #[α]
  let prodTy ← mkAppM ``Prod #[mkConst ``Nat, genα]
  let pairs' ← (pairs.zip rs).mapM fun ((w, _), r) => mkAppM ``Prod.mk #[w, r.expr]
  let gs' ← mkListLit prodTy pairs'
  -- Weights unchanged, so `h` retypes at `gs'` by defeq. Check it rather than trust the reduction.
  let hty := (← inferType h).replace fun x => if x == gs then some gs' else none
  unless ← isDefEq (← inferType h) hty do
    throwError "transform: rebuilt `frequency` weights do not retype its positivity proof; \
      expected{indentExpr hty}"
  let h' ← mkExpectedTypeHint h hty
  -- `gs.map (fun p => (p.1, support p.2)) = gs'.map …`, folded from the per-branch proofs.
  let propTy ← mkArrow α (mkSort .zero)
  let eltTy ← mkAppM ``Prod #[mkConst ``Nat, propTy]
  let consFn := mkAppN (mkConst ``List.cons [Level.zero]) #[eltTy]
  let mut hgMap ← mkEqRefl (← mkListLit eltTy [])
  for ((w, g), r) in (pairs.zip rs).reverse do
    let pg ← match r.proof? with
      | some p => pure p
      | none   => mkEqRefl (← mkSupport g)
    let pairW ← withLocalDeclD `s propTy fun s => do
      mkLambdaFVars #[s] (← mkAppM ``Prod.mk #[w, s])
    hgMap ← mkCongr (← mkCongrArg consFn (← mkCongrArg pairW pg)) hgMap
  let mapFn ← withLocalDeclD `p prodTy fun p => do
    let fst ← mkAppM ``Prod.fst #[p]
    let snd ← mkSupport (← mkAppM ``Prod.snd #[p])
    mkLambdaFVars #[p] (← mkAppM ``Prod.mk #[fst, snd])
  let hg ← mkExpectedTypeHint hgMap
    (← mkEq (← mkAppM ``List.map #[mapFn, gs]) (← mkAppM ``List.map #[mapFn, gs']))
  let e' ← mkAppOptM ``PGen.frequency #[α, gs', h']
  let proof ← mkAppOptM ``support_frequency_congr #[α, gs, gs', hg, h, h']
  return some { expr := e', proof? := some proof }

/-- Rewrite the children of `e` via the `@[gen_congr]` lemma for its head, proving
`support e = support e'`. A head with no lemma is fine only if there is nothing to descend into.

Fails loudly if encountering a `PGen`-valued argument with no lemma. -/
private partial def transformChildren (pass : HeadRewrite) (table : Array CongrRule) (depth : Depth)
    (e : Expr) : MetaM TransformResult := do
  if let some r ← transformOneOfChildren? pass table depth e then return r
  if let some r ← transformFrequencyChildren? pass table depth e then return r
  let some head := e.getAppFn.constName? | return { expr := e, proof? := none }
  -- Under a registered `X.unfold`, the argument descended into is its step, whose binder 0 is the
  -- recursion's depth.
  let entering := (unfoldNameMap (← getEnv))[head]?
  let some (_, congrName, diff) := table.find? (·.1 == head)
    | do
      -- Matchers/recursors carry PGen-valued arms but aren't descended structurally; don't flag.
      let isRec := match (← getEnv).find? head with
        | some (.recInfo _) => true
        | _ => false
      let auxiliary := (← Meta.getMatcherInfo? head).isSome || isRec
      -- `oneOf`/`frequency` reach here only when their by-hand descent above *declined* (no branch
      -- changed); both throw on shapes they cannot descend, so this really is "nothing to rewrite".
      -- Do not add a third combinator to this exemption without giving it a descent first.
      let listCarrier := head == ``PGen.oneOf || head == ``PGen.frequency
      if !auxiliary && !listCarrier && (← e.getAppArgs.anyM isGenValued) then
        throwError "transform: `{head}` has a PGen-valued argument but no `@[gen_congr]` \
          congruence lemma to descend through it; tag its support-congruence lemma `@[gen_congr]`"
      return { expr := e, proof? := none }
  let args := e.getAppArgs
  let mut newArgs := args
  let mut hyps := #[]
  let mut changed := false
  for i in diff do
    let (arg', h?) ← transformBinder pass table depth entering args[i]!
    newArgs := newArgs.set! i arg'
    match h? with
    | some h => hyps := hyps.push h; changed := true
    | none   => hyps := hyps.push (← mkBinderRefl args[i]!)
  unless changed do return { expr := e, proof? := none }
  let node' := mkAppN e.getAppFn newArgs
  return { expr := node', proof? := some (← mkCongrProof congrName e node' hyps) }

/-- Transform a child argument under its leading binders, returning the rebuilt argument and (when
changed) `∀ xs, support (arg xs) = support (arg' xs)`. -/
private partial def transformBinder (pass : HeadRewrite) (table : Array CongrRule) (depth : Depth)
    (entering : Option Name) (f : Expr) : MetaM (Expr × Option Expr) := do
  forallTelescope (← inferType f) fun xs _ => do
    let depth :=
      match entering, xs[0]? with
      | some typeName, some d => some (d, typeName)
      | _, _ => depth
    -- `f` is a subterm of an already-reduced node, so `f.beta xs` is reduced; descend directly.
    let r ← transformReduced pass table depth (f.beta xs)
    let f' ← mkLambdaFVars xs r.expr
    match r.proof? with
    | none => return (f', none)
    | some p => return (f', some (← mkLambdaFVars xs p))

end

/-- Transform `e0` based on a term rewrite `pass`, using congruence lemmas in `table` to prove
equivalence on the way. -/
def transform (pass : HeadRewrite) (table : Array CongrRule) (depth : Depth) (e0 : Expr) :
    MetaM TransformResult := do
  transformReduced pass table depth (← reduceExpr e0)

end Palamedes
