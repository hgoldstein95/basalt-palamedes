/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Derive.Util

/-!
# The Fusion Family and `s_unfold`

`X.merge_accuM` and the four `fold_accu_Option_*` bridges that `unfold_strategy` reads, plus
`X.s_unfold` — the `CorrectGen` combinator the search applies, certified against `X.accuM`.
-/

open Lean Elab Command Meta
open Lean.Parser.Term (matchAltExpr matchAlt)
open Palamedes Palamedes.PGen Palamedes.PGen.Support

namespace Palamedes.Derive

/-- `merge_accuM`: running two accumulating folds separately agrees with running the pairwise-merged
one. Statement and proof are constructor-indexed instances of the hand-written `Tree.merge_accuM`.
-/
def genMergeAccuM (ctx : Ctx) : CommandElabM Unit := do
  let sig1 := gid "σ1"; let sig2 := gid "σ2"; let bt1 := gid "β1"; let bt2 := gid "β2"
  let s1 := gid "s1"; let s2 := gid "s2"; let r1 := gid "r1"; let r2 := gid "r2"
  let t := gid "t"; let p := gid "p"
  let accuRef := ctx.ref "accuM"
  let self ← ctx.selfTy
  let opt := mkCIdent ``Option
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
  let cases ← ctx.ctors.mapIdxM fun ci c => do
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
      let fwdPats1 := interleavePairs xs hxs
      let fwdPats2 := interleavePairs ys hys
      let fwd ← seqTac (#[
        ← `(tactic| intro $H:ident),
        ← `(tactic| obtain ⟨$H1:ident, $H2:ident⟩ := $H),
        ← `(tactic| simp only [$accuLem:term, Option.bind_eq_bind, Option.bind_eq_some_iff]
              at $H1:ident $H2:ident ⊢),
        ← `(tactic| obtain $(← rcasesTuple (fwdPats1.push H1)):rcasesPat := $H1),
        ← `(tactic| obtain $(← rcasesTuple (fwdPats2.push H2)):rcasesPat := $H2)]
        ++ replaces ++ #[← `(tactic| simp_all)])
      let bwdPats := interleavePairs pxs hps
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
      let tac ← mkIffSplit fwd bwd
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

/-- `fold_accu_Option_basic`: a plain fold agrees with the accumulating monadic fold whose algebra
it matches (trivial state, `Option` monad, carrier `β`). -/
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
  let unitPat ← rcTuple #[]
  let bwdPats :=
    (interleavePairs ((Array.range k).map fun _ => unitPat)
      (hvs.map fun h => (h : TSyntax `rcasesPat))).push (hf : TSyntax `rcasesPat)
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
  mkIffSplit fwd bwd

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
  mkIffSplit fwd bwd

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
  let cases ← ctx.ctors.mapIdxM fun ci c => do
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
  let opt := mkCIdent ``Option
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
  let cases ← ctx.ctors.mapIdxM fun ci c => do
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
      let holes : Array Term ← (Array.range k).mapM fun _ => `(_)
      let mps ← (Array.range k).mapM fun j => do
        let ih : Ident := ihs[j]!
        `(($ih).mp rfl)
      let wits := (interleavePairs holes mps).push (hf : Term)
      let fwd ← seqTac #[
        ← `(tactic| intro $hf:ident),
        ← `(tactic| rw [$foldLem:term, $hC:term] at $hf:ident),
        ← `(tactic| simp only [$accuLem:term, Option.bind_eq_bind, Option.bind_eq_some_iff]),
        ← `(tactic| exact ⟨$wits,*⟩)]
      let bwdPats := interleavePairs vs hvs
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
      let tac ← mkIffSplit fwd bwd
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
  let cases ← ctx.ctors.mapIdxM fun ci c => do
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
  let opt := mkCIdent ``Option
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
  let disjuncts ← ctx.ctors.mapIdxM fun ci c => do
    let fC : Ident := fIds[ci]!
    let inner ← `($fC $(c.fieldIds)* $sg = some $bg ∧ $tv = $(c.fCtor) $(c.fieldIds)*)
    mkExists (c.nonRecIds ++ c.recFields.map (·.id)) inner
  let disj ← disjuncts[0:disjuncts.size-1].toArray.foldrM (fun d acc => `($d ∨ $acc)) disjuncts.back!
  let baseβ ← ctx.baseTy (β : Term)
  let gTy ← `(($bg : $β) → ($sg : $σ) → Palamedes.CorrectGen fun ($tv : $baseβ) => $disj)
  binders := binders.push (← expB g gTy)
  -- the step generator
  let alts ← ctx.ctors.mapIdxM fun ci c => do
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
  let cases ← ctx.ctors.mapIdxM fun ci c => do
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
        let namedPats (pre : String) : Array (TSyntax `rcasesPat) :=
          (Array.range k).map fun j => (gid s!"{pre}{j+1}" : TSyntax `rcasesPat)
        let pats :=
          (interleavePairs (namedPats "b") (namedPats "s")).push
            (← rcTuple #[(tv : TSyntax `rcasesPat),
              (htv : TSyntax `rcasesPat), (h : TSyntax `rcasesPat)])
            ++ namedPats "h"
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
        let (seeded, seedIds) := interleaved c "b"
        let hIds := (Array.range k).map fun j => gid s!"h{j+1}"
        let obtPats := interleavePairs seedIds hIds
        -- the base-functor witness over the seeds
        let fArgs : Array Term := seeded.map fun i => (i : Term)
        let fWit ← `($(c.fCtor) $fArgs*)
        let projs ← (Array.range k).mapM fun j => projComp stApp j k
        let mut parts := interleavePairs (seedIds.map fun i => (i : Term)) projs
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
    let tac ← mkIffSplit mp mpr
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

end Palamedes.Derive
