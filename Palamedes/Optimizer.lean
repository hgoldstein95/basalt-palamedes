/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.GenTransform

/-!
# Optimizer

The optimizer rewrites a synthesized `PGen`: it floats `assume`s up to the nearest choice point,
discharges the satisfiable ones, and flattens `pick` trees into uniform `oneOf`s.
-/

open Lean Elab Command Term Meta

namespace Palamedes

open Palamedes.PGen

/-- A rewrite result: the rewritten `expr` and the twin `support_*` lemma justifying it. Its
orientation is recovered when the proof is built (`mkLeafProof`). -/
abbrev GenRewriteResult := Expr × Name

mutual

/-- Determines if a given `assume` inside `e` can bubble up to its head. -/
partial def assumeReachesHead (e : Expr) (crossed : Array FVarId) : MetaM Bool := do
  match_expr ← withReducible (reduce e) with
  | assume _ b g =>
    if crossed.all (fun fv => !b.containsFVar fv) then return true
    else assumeUnderBinder g crossed -- a deeper assume commutes up past this stuck one
  | bind _ _ _ _ x f =>
    match_expr x with
    | pure _ _ _ a => assumeReachesHead (f.beta #[a]) crossed
    | _ => return (← assumeReachesHead x crossed) || (← assumeUnderBinder f crossed)
  | pick _ x y => return (← assumeReachesHead x crossed) || (← assumeReachesHead y crossed)
  | dite _ _ _ t f => return (← assumeUnderBinder t crossed) || (← assumeUnderBinder f crossed)
  | ite _ _ _ t f => return (← assumeReachesHead t crossed) || (← assumeReachesHead f crossed)
  | _ => return false

/-- Descend under one leading binder. A value binder enters `crossed`; a proof binder does not. -/
partial def assumeUnderBinder (f : Expr) (crossed : Array FVarId) : MetaM Bool := do
  forallBoundedTelescope (← inferType f) (some 1) fun xs _ => do
    let #[x] := xs | return false
    let crossed := if ← Meta.isProof x then crossed else crossed.push x.fvarId!
    assumeReachesHead (f.beta #[x]) crossed

end

/-- The two arms of a `dite P`, each built under its own hypothesis binder: `fun h : P => mkT h`
and `fun h : ¬P => mkF h`. -/
private def mkDiteArms (P : Expr) (mkT mkF : Expr → MetaM Expr) : MetaM (Expr × Expr) := do
  let t ← withLocalDecl `h .default P fun h => do mkLambdaFVars #[h] (← mkT h)
  let f ← withLocalDecl `h .default (.app (.const ``Not []) P) fun h => do
    mkLambdaFVars #[h] (← mkF h)
  return (t, f)

/-- `dite P (fun h => mkT h) (fun h => mkF h)`. `inst?` supplies the `Decidable` instance when the
matched term already carries one; otherwise it is synthesized. -/
private def mkDite (P : Expr) (inst? : Option Expr) (mkT mkF : Expr → MetaM Expr) : MetaM Expr := do
  let (t, f) ← mkDiteArms P mkT mkF
  match inst? with
  | some inst => mkAppOptM ``dite #[none, P, inst, t, f]
  | none => mkAppM ``dite #[P, t, f]

/-- Single head rewrite of a `bind` node `x >>= f`, with the twin `support_*` lemma justifying it. -/
def optimizeBind? (x f : Expr) : MetaM (Option GenRewriteResult) :=
  match_expr x with
  -- pure_bind : pure a >>= f ~~> f a
  | pure _ _ _ a => return some (Expr.app f a, ``support_pure_bind)
  -- bind_bind : (x >>= f) >>= g ~~> x >>= (fun x -> f x >>= g)
  | bind _ _ _ _ x' g => do
    let .forallE _ argTy _ _ ← inferType g | return none
    let f' ← withLocalDecl `a .default argTy fun a => do
      mkLambdaFVars #[a] (← mkAppM ``bind #[.app g a, f])
    return some (← mkAppM ``bind #[x', f'], ``support_bind_bind)
  -- assume_bind : assume b g >>= f ~~> assume b (fun h => g h >>= f)
  | assume _ b g => do
    let f' ← withLocalDecl `h .default (← mkEq b (.const ``true [])) fun h => do
      mkLambdaFVars #[h] (← mkAppM ``bind #[.app g h, f])
    return some (← mkAppM ``assume #[b, f'], ``support_assume_bind)
  -- Push the bind down through a branch (`pick`/`dite`/`ite`), duplicating `f`. Gated on
  -- `assumeReachesHead`: distribute only when a resulting arm exposes a liftable assume, which is
  -- what bounds the term-size blowup nested picks would otherwise cause.
  | pick _ x y => do
    let xb ← mkAppM ``bind #[x, f]
    let yb ← mkAppM ``bind #[y, f]
    unless (← assumeReachesHead xb #[]) || (← assumeReachesHead yb #[]) do return none
    return some (← mkAppM ``pick #[xb, yb], ``support_pick_bind)
  | dite _ P _ trueCase falseCase => do
    let (trueCase', falseCase') ← mkDiteArms P (fun h => mkAppM ``bind #[.app trueCase h, f])
                                              (fun h => mkAppM ``bind #[.app falseCase h, f])
    unless (← assumeUnderBinder trueCase' #[]) || (← assumeUnderBinder falseCase' #[]) do return none
    return some (← mkAppM ``dite #[P, trueCase', falseCase'], ``support_dite_bind)
  | ite _ P _ trueCase falseCase => do
    let trueCase' ← mkAppM ``bind #[trueCase, f]
    let falseCase' ← mkAppM ``bind #[falseCase, f]
    unless (← assumeReachesHead trueCase' #[]) || (← assumeReachesHead falseCase' #[]) do return none
    return some (← mkAppM ``ite #[P, trueCase', falseCase'], ``support_ite_bind)

  | _ => do
    lambdaBoundedTelescope f 1 fun args body => do
      -- bind_assume : x >>= fun a => assume b g ~~> assume b (fun h => x >>= fun a => g h),
      -- valid only if `b` avoids `a`. Conservative: a metavariable `b` possibly depending on `a`
      -- slips past `containsFVar`, so decline rather than risk a malformed term.
      let #[a] := args | return none
      let_expr assume _ b g := body | return none
      if b.containsFVar a.fvarId! then return none
      let f' ← withLocalDecl `h .default (← mkEq b (.const ``true [])) fun h => do
        mkLambdaFVars #[h] (← mkAppM ``bind #[x, ← mkLambdaFVars #[a] (.app g h)])
      return some (← mkAppM ``assume #[b, f'], ``support_bind_assume)

/-- Single head rewrite of an `assume` node. A decidably-*true*, closed, mvar-free guard never
filters, so `assume b f ~~> f h`. -/
def optimizeAssume? (b f : Expr) : MetaM (Option GenRewriteResult) := do
  if b.hasExprMVar then return none
  unless ← isDefEq b (.const ``true []) do return none
  let h ← mkDecideProof (← mkEq b (.const ``true []))
  return some (f.beta #[h], ``support_assume_true)

/-- Single head rewrite of a `pick` node `pick x y`, with the twin `support_*` lemma. -/
def optimizePick? (x y : Expr) : MetaM (Option GenRewriteResult) :=
  match_expr x with
  | assume _ b f =>
    -- Two `assume`s of the same guard lift cleanly; any other `y` leaves `x`'s guard to degrade
    -- into a `dite`, whose false branch keeps `y` alone.
    let sameGuard : Option Expr :=
      match_expr y with
      | assume _ b' g => if b == b' then some g else none
      | _ => none
    match sameGuard with
    | some g => do
      let c ← mkEq b (.const ``true [])
      let f' ← withLocalDecl `h .default c fun h => do
        mkLambdaFVars #[h] (← mkAppM ``pick #[.app f h, .app g h])
      return some (← mkAppM ``assume #[b, f'], ``support_pick_assume_same)
    | none => do
      let c ← mkEq b (.const ``true [])
      let e' ← mkDite c none (fun h => mkAppM ``pick #[.app f h, y]) (fun _ => pure y)
      return some (e', ``support_assume_pick)
  | _ =>
    match_expr y with
    -- Only `y` is an `assume`.
    | assume _ b f => do
      let c ← mkEq b (.const ``true [])
      let e' ← mkDite c none (fun h => mkAppM ``pick #[x, .app f h]) (fun _ => pure x)
      return some (e', ``support_pick_assume)
    | _ => return none

/-! ## Pick Flattening -/

/-- Match `oneOf (x :: xs) h` with a literal branch list, returning the head and the tail's
elements. -/
private def oneOfLit? (e : Expr) : Option (Expr × List Expr) :=
  match e.getAppFnArgs with
  | (``PGen.oneOf, #[_, gs, _]) =>
    match gs.getAppFnArgs with
    | (``List.cons, #[_, x, xs]) => do
      let elems ← listLitElems? xs
      return (x, elems)
    | _ => none
  | _ => none

/-- Flatten `pick x y` into one uniform `oneOf`: each arm contributes its elements if it is a literal
`oneOf` and itself otherwise. -/
private def flattenPick? (e : Expr) : MetaM (Option GenRewriteResult) := do
  match_expr e with
  | PGen.pick _ x y => do
    let (elems, lemmaName) :=
      match oneOfLit? x, oneOfLit? y with
      | none, none => ([x, y], ``support_pick_flatten)
      | some (xh, xelems), none => (xh :: xelems ++ [y], ``support_pick_flatten_left)
      | none, some (yh, yelems) => (x :: yh :: yelems, ``support_pick_flatten_right)
      | some (xh, xelems), some (yh, yelems) =>
        (xh :: xelems ++ yh :: yelems, ``support_pick_flatten_both)
    let tl ← mkListLit (← inferType x) elems.tail
    let gs ← mkAppM ``List.cons #[elems.head!, tl]
    let hne ← mkAppM ``List.cons_ne_nil #[elems.head!, tl]
    let e' ← mkAppM ``PGen.oneOf #[gs, hne]
    return some (e', lemmaName)
  | _ => return none

/-! ## Distributing Choices into `dite` -/

/-- Match `@dite α P inst t f`, returning `(P, inst, t, f)`. -/
private def matchDite? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  match_expr e with
  | dite _ P inst t f => some (P, inst, t, f)
  | _ => none

/-- Distribute a choice into a `dite` arm: `pick x (dite c t f) ~~> dite c (pick x t) (pick x f)`.

The copied arm (`x`/`y`) is duplicated into both branches, so this fires only when that arm is a leaf
(0 recursive holes); a recursive arm is left nested rather than blown up. -/
private def distributeChoiceDite? (depth : Depth) (e : Expr) : MetaM (Option GenRewriteResult) := do
  let some (_, typeName) := depth | return none
  let_expr PGen.pick _ x y := e | return none
  let holes ← baseCtorHoles (typeName.appendAfter "F")
  match matchDite? y with
  | some (P, inst, t, f) =>
    if (← branchHoles holes x) != 0 then return none
    let e' ← mkDite P (some inst) (fun h => mkAppM ``pick #[x, .app t h])
                           (fun h => mkAppM ``pick #[x, .app f h])
    return some (e', ``support_pick_dite_right)
  | none =>
  match matchDite? x with
  | some (P, inst, t, f) =>
    if (← branchHoles holes y) != 0 then return none
    let e' ← mkDite P (some inst) (fun h => mkAppM ``pick #[.app t h, y])
                           (fun h => mkAppM ``pick #[.app f h, y])
    return some (e', ``support_pick_dite_left)
  | none => return none

/-! ## The passes -/

/-- Turn a pass's chosen rewrite into a `HeadRewrite`, orienting its twin lemma into a
`support`-preservation proof. -/
private def withLeafProof (rw : Depth → Expr → MetaM (Option GenRewriteResult)) : HeadRewrite :=
  fun depth e => do
    let some (e', lemmaName) ← rw depth e | return none
    return some (e', ← mkLeafProof lemmaName e e')

/-- The monad-law / assume-floating pass: one head rewrite per node. -/
private def mainPass : HeadRewrite := withLeafProof fun _depth e =>
  match_expr e with
  | bind _ _ _ _ x f => optimizeBind? x f
  | pick _ x y => optimizePick? x y
  | assume _ b f => optimizeAssume? b f
  | _ => pure none

/-- The pick-collapsing pass. A choice is pushed into a `dite` arm first, before `flattenPick?`
would bury it, so each constructor gets its own flat `oneOf`; the pass then flattens the resulting
`pick` arms. -/
private def flattenPass : HeadRewrite := withLeafProof fun depth e => do
  if let some r ← distributeChoiceDite? depth e then return some r
  flattenPick? e

/-- Optimize a raw `PGen`, returning the optimized term with a proof its `support` is unchanged.
`mainPass` to a fixed point, then `flattenPass` — which also distributes choices into `dite`
arms so each constructor is a separately addressable `oneOf`, the shape the tuning pass needs. -/
def optimizeGen (e : Expr) : MetaM (Expr × Expr) := do
  let table := getGenCongrRules (← getEnv)
  let r1 ← transform mainPass table none e
  let r2 ← transform flattenPass table none r1.expr
  let expr := r2.expr
  let proof ←
    match ← chainProofs #[r1.proof?, r2.proof?] with
    | some p => mkExpectedTypeHint p (← mkEq (← mkSupport e) (← mkSupport expr))
    | none => mkSupportRefl e
  return (expr, proof)

end Palamedes
