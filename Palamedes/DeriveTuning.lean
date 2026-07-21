import Palamedes.Optimizer
import Palamedes.Laws
import Palamedes.Synthesizer.FrontEnd

/-!
# `derive_tuning` — make a synthesized generator `θ`-addressable

`derive_tuning genFoo` emits, for a synthesized generator, the declarations `tunable def` gives a
hand-written one:

* `genFoo.tuned (θ : Tuning) …` — every `frequency` weight read from `θ`;
* `genFoo.defaults : Tuning` — the uniform weighting; a `SchedulePolicy` is materialized into a
  separate `Tuning`, never baked into the term;
* `genFoo.sites : Array Site` — offsets, arities, per-branch recursive-child counts;
* `genFoo.tuned_defaults : ∀ args, genFoo.tuned genFoo.defaults args = genFoo args`, definitionally
  (carrier shape only — see below);
* `genFoo.tuned_support` / `genFoo.tuned_sound_complete` — the support invariant across every `θ`,
  and (when the generator carries a `sound_complete`) the law restated for every `θ`.

It runs post-elaboration, where the recursion is the `unfold` combinator rather than an `Order.fix`,
so threading `θ` is a support-preserving rewrite of the `oneOf` sites with no fixpoint to rebuild.

**The rewrite substrate is always the `Palamedes.PGen` carrier.** `installTuning` keys on the
carrier's `PGen.oneOf`, and the optimizer's `support lhs = support rhs` chaining does not typecheck
at an abstract `G` — so a Basalt-shaped generator is never rewritten *in place*. Instead it is tuned
through its **carrier companion** `genFoo.gen`, which `correct def` emits alongside the projection:

* the companion is tuned exactly as a carrier declaration would be (the emissions land under
  `genFoo.gen.*`);
* `genFoo.tuned (θ : Tuning) …` is then *re-projected*: for a total generator (`G α`) the
  `totality` cascade is re-run on the θ-open tuned term — `total_frequency` never inspects
  weights — and the witness is extracted back to generator code; for a filtering generator
  (`G (Option α)`) the tuned companion goes through `totalize`, no witness needed;
* `genFoo.tuned_sound_complete` transfers the carrier law across the fresh witness
  (`isSoundAndComplete_of_total`) for the total shape, and across the `someSupport` bridge
  (`isSomeSoundAndComplete_of_someSupport`) for the filtering shape.

There is **no Basalt-level `tuned_defaults`**: the projected `tuned defaults` and the original
projection run through *different* totality witnesses, and two witnesses of the same generator are
not definitionally equal — the carrier-level `genFoo.gen.tuned_defaults` carries that fact instead.

A plain-`def` Basalt-shaped generator has no companion to tune — `generator_search` is a tactic and
never learns a declaration name — so `derive_tuning` rejects it with the fix: use `correct def`.
-/

open Lean Elab Command Meta

namespace Palamedes

syntax (name := deriveTuning) "derive_tuning " ident : command

/-- The carrier tuning path: `buildTuned`, the four structural declarations, `tuned_support`, and —
when `declName.sound_complete` exists and has the carrier's `support = P` shape — the
`tuned_sound_complete` law. Returns whether the law was emitted. Reporting is the caller's, so the
Basalt path can fold the companion's emissions into one message. -/
def runCarrierTuning (declName : Name) : CommandElabM Bool := do
  let some ci := (← getEnv).find? declName
    | throwError "derive_tuning: unknown constant {declName}"
  let some v := ci.value?
    | throwError "derive_tuning: {declName} has no value to reweight"
  let lvls := ci.levelParams
  let res ← liftTermElabM do
    let res ← Palamedes.buildTuned declName (← instantiateMVars v)
    Meta.check res.tuned
    pure res
  let ⟨tunedVal, sites, total, supportProof⟩ := res
  -- Absolute names via `addDecl`/`addAndCompile`, so an enclosing `namespace` cannot re-prefix them.
  liftTermElabM do
    let tunedName := declName ++ `tuned
    let defaultsName := declName ++ `defaults
    let sitesName := declName ++ `sites
    -- `addAndCompile`, not `addDecl`: `#genstats`/`#eval` run these, so they need compiled code.
    let addC (name : Name) (type value : Expr) : MetaM Unit :=
      addAndCompile <| .defnDecl {
        name, levelParams := lvls, type, value, hints := .regular 0, safety := .safe }
    addC tunedName (← inferType tunedVal) tunedVal
    let defaultsVal := mkApp (mkConst ``Tuning.mk) (toExpr (Array.replicate total ((1, 0) : Nat × Nat)))
    addC defaultsName (mkConst ``Tuning) defaultsVal
    let siteExprs ← sites.toList.mapM fun s => pure <|
      mkAppN (mkConst ``Site.mk) #[toExpr s.name, toExpr s.offset, toExpr s.arity, toExpr s.holes]
    let sitesVal ← mkAppM ``List.toArray #[← mkListLit (mkConst ``Site) siteExprs]
    addC sitesName (← mkAppM ``Array #[mkConst ``Site]) sitesVal
    -- `∀ args, gen.tuned defaults args = gen args`, bound at the `Expr` level so the generator's own
    -- implicit/explicit arguments are quantified rather than left as metavariables. `Eq.refl` typed at
    -- `lhs = rhs` makes the kernel check `lhs ≡ rhs` at full transparency, which holds because
    -- `Tuning.weight defaults i d` reduces to the weight `1` that `oneOf` already carries.
    let defaultsC := mkConst defaultsName
    let tunedC := mkConst tunedName (lvls.map .param)
    let declC := mkConst declName (lvls.map .param)
    forallTelescope ci.type fun args _ => do
      let lhs := mkAppN (.app tunedC defaultsC) args
      let rhs := mkAppN declC args
      let stmt ← mkForallFVars args (← mkEq lhs rhs)
      let proof ← mkLambdaFVars args (← mkEqRefl lhs)
      addDecl <| .thmDecl {
        name := declName ++ `tuned_defaults, levelParams := lvls, type := stmt, value := proof }
    -- `∀ θ args, support (gen.tuned θ args) = support (gen args)` — the theorem `installTuning`
    -- proves at every site, so `.tuned` carries the `support = P` invariant rather than merely
    -- happening to preserve it. Stated against the emitted constants (not the
    -- raw bodies) and checked against the proof's own type, since the two telescopes are built
    -- independently — from `ci.type` here, from the value in `buildTuned`.
    withLocalDeclD `θ (mkConst ``Tuning) fun θ => do
      forallTelescope ci.type fun args _ => do
        let lhs ← mkAppM ``PGen.support #[mkAppN (.app tunedC θ) args]
        let rhs ← mkAppM ``PGen.support #[mkAppN declC args]
        let stmt ← mkForallFVars (#[θ] ++ args) (← mkEq lhs rhs)
        unless ← isDefEq (← inferType supportProof) stmt do
          throwError "derive_tuning: the support-preservation proof does not match\
            {indentExpr stmt}\nproof has type{indentExpr (← inferType supportProof)}"
        addDecl <| .thmDecl {
          name := declName ++ `tuned_support, levelParams := lvls, type := stmt,
          value := ← mkExpectedTypeHint supportProof stmt }
  -- `∀ θ args, IsSoundAndComplete ((gen.tuned θ args).run (G := SPMF)) P` — the law in **Basalt's**
  -- vocabulary, when the generator has one to carry. Only `correct def` establishes `gen.support = P`
  -- (a plain `def` has no `P` to speak of), so this is emitted conditionally, and reported either
  -- way — a law that appears only sometimes must not appear *silently* only sometimes.
  liftTermElabM do
    let scName := declName ++ `sound_complete
    let some sc := (← getEnv).find? scName | return false
    -- Check the *statement*, not just the name: a conventionally-named theorem saying something
    -- else must not be chained into a law about the tuned generator.
    let ok ← forallTelescope sc.type fun _ body => do
      let some (_, lhs, _) := body.eq? | return false
      return lhs.isAppOf ``PGen.support
    unless ok do return false
    withLocalDeclD `θ (mkConst ``Tuning) fun θ => do
      forallTelescope ci.type fun args _ => do
        let tsC := mkConst (declName ++ `tuned_support) (lvls.map .param)
        let scC := mkConst scName (lvls.map .param)
        -- `(gen.tuned θ args).support = gen.support = P`, then across to Basalt's law. The statement
        -- is read off the bridge lemma's own conclusion rather than rebuilt, so it is canonical by
        -- construction — there are no two independently-built telescopes to reconcile here.
        let chain ← mkAppM ``Eq.trans #[mkAppN (.app tsC θ) args, mkAppN scC args]
        let proof ← mkAppM ``Palamedes.isSoundAndComplete_of_support #[chain]
        let stmt ← mkForallFVars (#[θ] ++ args) (← instantiateMVars (← inferType proof))
        let value ← mkLambdaFVars (#[θ] ++ args) (← instantiateMVars proof)
        if value.hasExprMVar || stmt.hasExprMVar then
          throwError "derive_tuning: `tuned_sound_complete` still has metavariables"
        addDecl <| .thmDecl {
          name := declName ++ `tuned_sound_complete, levelParams := lvls, type := stmt, value }
        return true

/-- Re-project a tuned carrier companion to the Basalt shape and transfer its law.

Emits `declName.tuned : Tuning → <declName's own type>` (plus `defaults`/`sites` aliases of the
companion's) and, law permitting, `declName.tuned_sound_complete`. `filtering` follows the declared
shape: `G (Option α)` projects through `totalize`; `G α` re-runs the `totality` cascade on the
θ-open tuned term and extracts the witness back to generator code. Returns `none` if the law was
emitted, or `some reason` naming why it was not. -/
def emitBasaltTuned (declName companion : Name) (filtering : Bool) :
    CommandElabM (Option MessageData) := do
  let some ci := (← getEnv).find? declName
    | throwError "derive_tuning: unknown constant {declName}"
  let some tunedCi := (← getEnv).find? (companion ++ `tuned)
    | throwError "derive_tuning: internal — {companion}.tuned was not emitted"
  -- Every `mkConst` below names the companion's declarations without level arguments, which is only
  -- right because `correct def` — the sole emitter of companions — makes them monomorphic.
  unless tunedCi.levelParams.isEmpty do
    throwError "derive_tuning: internal — {companion}.tuned is universe-polymorphic, which the \
      re-projection does not handle"
  let tunedVal := tunedCi.value!
  liftTermElabM <| withLocalDeclD `θ (mkConst ``Tuning) fun θ => do
    forallTelescope ci.type fun args body => do
      let G := body.getAppFn
      -- The value binders — everything that is neither `G` nor its `[Gen G]` instance — are the
      -- companion's whole telescope, in the same order (`correct def` built it from the same
      -- binders the same way).
      let valueArgs ← args.filterM fun x => do
        if x == G then return false
        let t ← whnf (← inferType x)
        return !(t.isAppOfArity ``Gen 1 && t.appArg! == G)
      let tunedBody := tunedVal.beta (#[θ] ++ valueArgs)
      let tunedApp := mkAppN (mkApp (mkConst (companion ++ `tuned)) θ) valueArgs
      let (emittedVal, hw?) ←
        if filtering then
          -- `G (Option β)`: the projection is `totalize`, applied to the *constant* so the emitted
          -- term reads as what it is. No witness enters the data path, so nothing to extract.
          let β := body.appArg!.appArg!
          pure (← mkAppOptM ``Palamedes.PGen.totalize #[some β, some tunedApp, some G, none], none)
        else
          -- `G α`: rebuild the totality witness on the θ-open tuned term — `total_frequency` never
          -- inspects weights, so the cascade closes exactly as it did pre-tuning — and project it
          -- back to generator code.
          let w ←
            try
              solveGoalWithTactic (← mkAppM ``Palamedes.PGen.total #[tunedBody])
                (← `(tactic| totality))
            catch e =>
              throwError "derive_tuning: could not rebuild the totality witness for the tuned \
                generator.\n{e.toMessageData}"
          let α := body.appArg!
          let tgen ← mkAppOptM ``Subtype.val #[none, none, w]
          let proj ← extractWitness
            (← mkAppOptM ``Palamedes.TGen.run #[some α, some tgen, some G, none])
          pure (proj, some w)
      Term.synthesizeSyntheticMVarsNoPostponing
      let stmt ← instantiateMVars (← mkForallFVars (#[θ] ++ args) body)
      let value ← instantiateMVars (← mkLambdaFVars (#[θ] ++ args) emittedVal)
      if value.hasExprMVar || stmt.hasExprMVar then
        throwError "derive_tuning: `tuned` still has metavariables after instantiation"
      addAndCompile <| .defnDecl {
        name := declName ++ `tuned, levelParams := [], type := stmt, value
        hints := .abbrev, safety := .safe }
      for suffix in [`defaults, `sites] do
        let some c := (← getEnv).find? (companion ++ suffix)
          | throwError "derive_tuning: internal — {companion ++ suffix} was not emitted"
        addAndCompile <| .defnDecl {
          name := declName ++ suffix, levelParams := [], type := c.type,
          value := mkConst (companion ++ suffix), hints := .abbrev, safety := .safe }

      -- The tuned law, transferred to the projected constant. The carrier chain
      -- `(companion.tuned θ args).support = companion.support = P` exists whenever the companion
      -- carries its law (always, for a `correct def` companion); the shape decides the bridge.
      let scName := companion ++ `sound_complete
      let some sc := (← getEnv).find? scName
        | return some m!"{companion} has no `sound_complete` to carry across"
      let ok ← forallTelescope sc.type fun _ scBody => do
        let some (_, lhs, _) := scBody.eq? | return false
        return lhs.isAppOf ``PGen.support
      unless ok do
        return some m!"{scName} is not a `PGen.support` equation, so there is no carrier law to chain"
      let tsApp := mkAppN (mkApp (mkConst (companion ++ `tuned_support)) θ) valueArgs
      let scApp := mkAppN (mkConst scName) valueArgs
      let chain ← mkAppM ``Eq.trans #[tsApp, scApp]
      let proof? : Expr ⊕ MessageData ←
        if filtering then
          -- `someSupport (tuned θ) = support (tuned θ)` for *this* tuned term, by simp over the
          -- combinator twins — the same per-generator discharge `correct def` performs, on a term
          -- whose weights are now opaque `θ`-reads. A missing twin fails here, and the reason is
          -- carried out rather than swallowed: the law is reported absent, and why.
          try
            let bridgeGoal ← mkEq (← mkAppM ``Palamedes.someSupport #[tunedBody])
              (← mkAppM ``Palamedes.PGen.support #[tunedBody])
            let bridge ← solveGoalWithTactic bridgeGoal (← `(tactic| simp))
            let hsome ← mkAppM ``Eq.trans #[bridge, chain]
            pure (.inl (← mkAppM ``Palamedes.isSomeSoundAndComplete_of_someSupport #[hsome]))
          catch e =>
            pure (.inr m!"the `someSupport` bridge could not be discharged — a combinator twin is \
              probably missing.\n{e.toMessageData}")
        else
          let some w := hw?
            | return some m!"internal — no totality witness on the total path"
          let hw ← mkAppOptM ``Subtype.property #[none, none, w]
          pure (.inl (← mkAppM ``Palamedes.isSoundAndComplete_of_total #[hw, chain]))
      let proof ← match proof? with
        | .inl p => pure p
        | .inr reason => return some reason
      -- State the law about the emitted constant at `SPMF`, reconciling with the proof's own
      -- conclusion (about the witness projection / `totalize` of the companion) by `isDefEq` — the
      -- same instantiation of the same term, checked by the kernel at `addDecl`.
      let spmf := Lean.mkConst ``SPMF [Level.zero]
      let inst ← synthInstance (← mkAppM ``Gen #[spmf])
      let lawArgs ← args.mapM fun x => do
        if x == G then return spmf
        let t ← whnf (← inferType x)
        if t.isAppOfArity ``Gen 1 && t.appArg! == G then return inst
        return x
      let atSPMF := mkAppN (mkApp (mkConst (declName ++ `tuned)) θ) lawArgs
      let proofTy ← inferType proof
      let law := if filtering then ``Palamedes.IsSomeSoundAndComplete else ``IsSoundAndComplete
      let pred := proofTy.appArg!
      let stmt ← mkAppM law #[atSPMF, pred]
      unless ← isDefEq proofTy stmt do
        throwError "derive_tuning: the tuned law does not match{indentExpr stmt}\n\
          proof has type{indentExpr proofTy}"
      let stmt ← instantiateMVars stmt
      let value ← instantiateMVars (← mkExpectedTypeHint proof stmt)
      let stmt ← mkForallFVars (#[θ] ++ valueArgs) stmt
      let value ← mkLambdaFVars (#[θ] ++ valueArgs) value
      if value.hasExprMVar || stmt.hasExprMVar then
        throwError "derive_tuning: `tuned_sound_complete` still has metavariables"
      addDecl <| .thmDecl {
        name := declName ++ `tuned_sound_complete, levelParams := [], type := stmt, value }
      return none

@[command_elab deriveTuning]
def elabDeriveTuning : CommandElab := fun stx => do
  let `(derive_tuning $genId) := stx | throwError "derive_tuning: invalid syntax"
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo genId
  let some ci := (← getEnv).find? declName
    | throwError "derive_tuning: unknown constant {declName}"
  -- Dispatch on the declared shape, mirroring `generator_search`: the carrier is rewritten in
  -- place; a Basalt-shaped declaration is tuned through its carrier companion and re-projected.
  let shape ← liftTermElabM <| forallTelescope ci.type fun args body => do
    if body.isAppOf ``Palamedes.PGen then
      return some none
    let hd := body.getAppFn
    if hd.isFVar && args.contains hd then
      return some (some (body.appArg!.isAppOfArity ``Option 1))
    return none
  match shape with
  | none =>
    throwError "derive_tuning: {declName} is neither a `Palamedes.PGen` nor a Basalt-shaped \
      generator, so there is nothing here to reweight."
  | some none =>
    let hasLaw ← runCarrierTuning declName
    let base := "tuned, defaults, sites, tuned_defaults, tuned_support"
    if hasLaw then
      logInfo m!"derive_tuning {declName}: emitted {base}, tuned_sound_complete"
    else
      logInfo m!"derive_tuning {declName}: emitted {base}\n  \
        (no `tuned_sound_complete`: {declName} has no `sound_complete` to carry across — \
        declare it with `correct def` to get one)"
  | some (some filtering) =>
    let companion := declName ++ `gen
    unless (← getEnv).contains companion do
      throwError "derive_tuning: {declName} is Basalt-shaped and has no carrier companion \
        ({companion}) to tune.\n\n\
        The tuning layer rewrites the `Palamedes.PGen` carrier, and the Basalt shape is a \
        projection of it — `generator_search` is a tactic and never learns a declaration name, so \
        only `correct def` keeps the carrier around. Re-declare it as\n\n  \
        correct def {declName} … := by generator_search …\n\n\
        and `derive_tuning {declName}` will tune the companion and re-project."
    -- The companion always carries a `sound_complete` (`correct def` emits both together), so a
    -- carrier tuning that declines to emit its law means the companion is malformed, not that the
    -- generator simply has none. `emitBasaltTuned` reports the specific reason either way.
    let _ ← runCarrierTuning companion
    let noLaw? ← emitBasaltTuned declName companion filtering
    let base := "tuned, defaults, sites"
    let carrier := m!"(tuned at the carrier: see {companion}.tuned_support and friends; \
      `tuned_defaults` exists only there — two totality witnesses of one generator are not \
      definitionally equal)"
    match noLaw? with
    | none =>
      logInfo m!"derive_tuning {declName}: emitted {base}, tuned_sound_complete\n  {carrier}"
    | some reason =>
      logInfo m!"derive_tuning {declName}: emitted {base}\n  \
        (no `tuned_sound_complete`: {reason})\n  {carrier}"

end Palamedes
