/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Derive.Util

/-!
# Recursion Schemes and Laws

`X.fold`, `X.accuM`, the `unfold` family (`unfoldGo`/`unfold`/`TGen.unfold` and their projection
equations), the support characterization at both interpretations, and the totality lemmas
`X.total_unfold`/`X.total_cases`.
-/

open Lean Elab Command Meta
open Lean.Parser.Term (matchAltExpr matchAlt)
open Palamedes Palamedes.PGen Palamedes.PGen.Support

namespace Palamedes.Derive

def genFold (ctx : Ctx) : CommandElabM Unit := do
  let β := gid "β"
  let t := gid "t"
  let foldRef := ctx.ref "fold"
  let self ← ctx.selfTy
  let fs := algIds ctx
  -- the algebra applied to a constructor's fields, with recursive positions folded
  let foldArgs (c : CtorData) : CommandElabM (Array Term) :=
    c.fields.mapM fun fd =>
      if fd.isRec then `($foldRef $fs* $(fd.id)) else pure (fd.id : Term)
  let binders := (← foldBinders ctx β true).push (← expB t self)
  let alts ← ctx.ctors.mapIdxM fun i c => do
    let pat ← `($(c.xCtor) $(c.fieldIds)*)
    let rhs ← `($(fs[i]!) $(← foldArgs c)*)
    `(matchAltExpr| | $pat:term => $rhs:term)
  addCmd (← `(command|
    def $(ctx.declId "fold"):ident $binders:bracketedBinder* : $β :=
      match $t:ident with $alts:matchAlt*))
  -- per-constructor simp lemmas
  for hi : i in [0:ctx.ctors.size] do
    let c := ctx.ctors[i]
    let lb := (← foldBinders ctx β false) ++ (← ctorBinders c self)
    let args ← foldArgs c
    let lemId := ctx.declId s!"fold_{c.short}"
    addCmd (← `(command|
      @[simp] theorem $lemId:ident $lb:bracketedBinder* :
          $foldRef $fs* ($(c.xCtor) $(c.fieldIds)*) = $(fs[i]!) $args* := rfl))

/-- Build `accuM`'s right-hand side for one constructor (shared by the def and its simp lemma). -/
def accuRhs (ctx : Ctx) (c : CtorData) (ci : Nat) (allArgs : Array Term) (s : Ident) :
    CommandElabM Term := do
  let accuRef := ctx.ref "accuM"
  let fIds := algIds ctx
  let recFs := c.recFields
  if recFs.isEmpty then
    return ← `($(fIds[ci]!) $(c.fieldIds.map (fun i => (i : Term)))* $s)
  let sIds := (Array.range recFs.size).map fun j => gid s!"s{j+1}"
  let (core, vIds) := interleaved c "v"
  let coreArgs : Array Term := core.map fun i => (i : Term)
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
  let binders ← accuBinders ctx β σ m true
  let allArgs := accuArgIds ctx
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
    let lb := (← accuBinders ctx β σ m false) ++ (← ctorBinders c self)
      |>.push (← impB #[s] (σ : Term))
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
    let (mkIds, vIds) := interleaved c "v"
    let mkArgs : Array Term := mkIds.map fun i => (i : Term)
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
  -- run_unfold. `@[partial_witness]` as well as `@[simp]`: stated at an arbitrary `G` with `Fail G`,
  -- it fires at `OptionT G` too, which is why a *filtering* recursive generator needs no second
  -- recursion scheme — `unfoldGo` is already polymorphic, so reading it there short-circuits on
  -- `none` by itself.
  addCmd (← `(command|
    @[simp, partial_witness] theorem $(ctx.declId "run_unfold"):ident $uBinders:bracketedBinder*
        ($f : Nat → $β → Palamedes.PGen $baseβ) ($b : $β) ($d₀ : Nat)
        ($G : Type → Type) [Gen $G] [Palamedes.Fail $G] :
        ($unfoldRef $f $b $d₀).run (G := $G) = $goRef (fun $d $x => ($f $d $x).run) $d₀ $b := rfl))
  -- The `TGen` twin of `run_unfold`. Tagged `@[totality_witness]` rather than `@[simp]`: this is what lets
  -- the emitted generator's recursion unfold from the totality witness back to `unfoldGo`, so a
  -- synthesized generator reads as a generator rather than as a proof term. No `Fail` constraint —
  -- that is the whole point of `TGen`.
  addCmd (← `(command|
    @[totality_witness] theorem $(ctx.declId "trun_unfold"):ident $uBinders:bracketedBinder*
        ($f : Nat → $β → Palamedes.TGen $baseβ) ($b : $β) ($d₀ : Nat)
        ($G : Type → Type) [Gen $G] :
        ($tgenRef $f $b $d₀).run (G := $G) = $goRef (fun $d $x => ($f $d $x).run) $d₀ $b := rfl))
  -- The derived layer's mirror equation, in the sense `Total.lean`'s `TGen.toGen_*` are: coercing a
  -- failure-free unfold is unfolding its coerced step. It is what lets a generator *defined* at
  -- `TGen` — the direction any assume-free generator should be spelled in, so that its totality
  -- witness is the definition rather than a re-spelling of it — still be reasoned about with the
  -- `PGen`-level `support_unfold` above. Not `@[simp]`: it is cited where a proof crosses the
  -- coercion, and nowhere else.
  addCmd (← `(command|
    theorem $(ctx.declId "toGen_unfold"):ident $uBinders:bracketedBinder*
        ($f : Nat → $β → Palamedes.TGen $baseβ) ($b : $β) ($d₀ : Nat) :
        Palamedes.TGen.toGen ($tgenRef $f $b $d₀)
          = $unfoldRef (fun $d $x => Palamedes.TGen.toGen ($f $d $x)) $b $d₀ := rfl))

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
      let (fs, bIds) := interleaved c "b"
      let fArgs : Array Term := fs.map fun i => (i : Term)
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

/-- Characterizes the support notion `genSupportUnfold` is emitting the characterization for. -/
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
  goInst : Option (CommandElabM Term)
  /-- Adapts an equation proof before feeding it to a constructor's injectivity lemma. On the
  `OptionT` side the equation is between `Option`s, so it needs peeling first. -/
  wrapInj : Term → CommandElabM Term

/-- The `PGen.support` kit. -/
def SupportKit.spmf : SupportKit where
  thmName := "support_unfold"
  supportOf := fun g => `(Palamedes.PGen.support $g)
  bindLem := mkCIdent ``SPMF.support_bind
  pureLem := mkCIdent ``SPMF.support_pure
  memLems := #[mkCIdent ``Set.mem_setOf_eq, mkCIdent ``Set.mem_singleton_iff]
  headSimp := #[mkCIdent ``Set.mem_setOf_eq]
  memWrap := pure
  runWrap := pure
  goInst := none
  wrapInj := pure

/-- The `someSupport` kit: the same script at `OptionT SPMF`. -/
def SupportKit.optionT : SupportKit where
  thmName := "someSupport_unfold"
  supportOf := fun g => `(Palamedes.someSupport $g)
  bindLem := mkCIdent ``Palamedes.mem_support_optionT_bind
  pureLem := mkCIdent ``Palamedes.support_optionT_pure
  memLems := #[mkCIdent ``Set.mem_singleton_iff]
  headSimp := #[]
  memWrap := fun w => `(some $w)
  runWrap := fun e => `(OptionT.run $e)
  goInst := some `(OptionT SPMF)
  wrapInj := fun h => `(Option.some.inj $h)

/-- `X.support_unfold` / `X.someSupport_unfold` — the support characterization, by a generated
per-constructor induction.

Because `unfold_support`'s step predicate is itself depth-indexed, the characterization holds at
every depth unconditionally: no depth-independence hypothesis is needed, and the per-constructor
scripts below are the same ones they were before depth threading. -/
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
    let ihIds := ihIdsFor recFs.size
    let tv := gid "tv"
    let ht := gid "ht"
    let hw := gid "hw"
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
          let pats := (interleavePairs vIds hvIds).push heq
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
    let bwd ← do
      if recFs.isEmpty then
        let h := gid "h"
        let wit ← `($(c.fCtor) $(c.fieldIds)*)
        seqTac #[
          ← `(tactic| intro $h:ident),
          ← `(tactic| exact ⟨$wit, $h, by simp only [$pureSet,*]⟩)]
      else
        let (wit', bIds) := interleaved c "b"
        let witArgs : Array Term := wit'.map fun i => (i : Term)
        let hb := gid "hb"
        let hIds := (Array.range recFs.size).map fun j => gid s!"h{j+1}"
        let mut pats : Array Ident := bIds
        pats := pats.push hb
        pats := pats ++ hIds
        let mprs ← (Array.range recFs.size).mapM fun j => do
          let ih : Ident := ihIds[j]!
          let hj : Ident := hIds[j]!
          `(($ih).mpr $hj)
        let final := (interleavePairs (recFs.map fun fd => (fd.id : Term)) mprs).push (← `(rfl))
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
      ← mkIffSplit fwd bwd]
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
    | some instM => do
        let inst ← instM
        `($goRef (G := $inst) (fun $d $x => ($f $d $x).run) $d₀ $b)
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
      ⟨$(rootedIdent ctx.tgenUnfoldName) (fun $d $y => ($h $d $y).val) $b $d₀, by
        have $heq:ident : (fun $d $y => (($h $d $y).val).toGen) = $g :=
          funext fun $d:ident => funext fun $y:ident => ($h $d $y).property
        conv_rhs => rw [← $heq:ident]
        ext; rfl⟩))

/-- The base functor's case-analysis totality lemma.

The synthesized step function ends in a `match` over the base functor, and `totality` has to get
past it. Doing that with `split` (or with a bare `cases`) puts a `splitter`/recursor in the
witness's data path, which blocks `.val` from projecting — so the emitted generator lands in the
environment as a proof term rather than as generator code. This lemma instead builds the witness
as a `match` producing `TGen`s, inside `TGen.mk`, so the `.run` projection cancels and what is
emitted reads exactly like a hand-written generator. -/
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
    let ihIds := ihIdsFor recFs.size
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

end Palamedes.Derive
