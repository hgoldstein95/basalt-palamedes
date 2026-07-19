import Palamedes.Optimizer

/-!
# `derive_tuning` — make a synthesized generator `θ`-addressable

`derive_tuning genFoo` emits, for a synthesized generator, the declarations `tunable def` gives a
hand-written one:

* `genFoo.tuned (θ : Tuning) …` — every `frequency` weight read from `θ`;
* `genFoo.defaults : Tuning` — the uniform weighting; a `SchedulePolicy` is materialized into a
  separate `Tuning`, never baked into the term;
* `genFoo.sites : Array Site` — offsets, arities, per-branch recursive-child counts;
* `genFoo.tuned_defaults : ∀ args, genFoo.tuned genFoo.defaults args = genFoo args`, definitionally.

It runs post-elaboration, where the recursion is the `unfold` combinator rather than an `Order.fix`,
so threading `θ` is a support-preserving rewrite of the `oneOf` sites with no fixpoint to rebuild.
-/

open Lean Elab Command Meta

namespace Palamedes

syntax (name := deriveTuning) "derive_tuning " ident : command

@[command_elab deriveTuning]
def elabDeriveTuning : CommandElab := fun stx => do
  let `(derive_tuning $genId) := stx | throwError "derive_tuning: invalid syntax"
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo genId
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
    -- proves at every site but used to discard, so `.tuned` carries the `support = P` invariant
    -- rather than merely happening to preserve it. Stated against the emitted constants (not the
    -- raw bodies) and checked against the proof's own type, since the two telescopes are built
    -- independently — from `ci.type` here, from the value in `buildTuned`.
    withLocalDeclD `θ (mkConst ``Tuning) fun θ => do
      forallTelescope ci.type fun args _ => do
        let lhs ← mkAppM ``Gen.support #[mkAppN (.app tunedC θ) args]
        let rhs ← mkAppM ``Gen.support #[mkAppN declC args]
        let stmt ← mkForallFVars (#[θ] ++ args) (← mkEq lhs rhs)
        unless ← isDefEq (← inferType supportProof) stmt do
          throwError "derive_tuning: the support-preservation proof does not match\
            {indentExpr stmt}\nproof has type{indentExpr (← inferType supportProof)}"
        addDecl <| .thmDecl {
          name := declName ++ `tuned_support, levelParams := lvls, type := stmt,
          value := ← mkExpectedTypeHint supportProof stmt }

end Palamedes
