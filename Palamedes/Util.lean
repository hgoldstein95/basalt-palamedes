/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Lean

/-!
# Meta-level helpers shared by the synthesizer and `derive_palamedes`

Two tactics, both used to close goals that arise from *elaborating against a metavariable* rather
than from the object logic:

* `rflm` closes `?f a₁ … aₙ = rhs` by assigning `?f := fun x₁ … xₙ => rhs[aᵢ := xᵢ]`. This is how the
  case-split rule synthesizes the motive `P` in `∀ {a}, P a scrut = Q a` (`CGeneratorSearch.lean`)
  and how `derive_palamedes` discharges the corresponding premise in its emitted scripts.
* `unfold_matches` unfolds the compiler-generated `match_*` auxiliaries that a `fold`/`accuM`
  equation leaves behind, so that `simp` can see through them.

`ensureLHSIsMVar` and `mkLambdaGeneralizeFVars` exist only to support `rflm`. (Both, and `rflm`
itself, are due to Kyle Miller.)
-/

open Lean Elab Meta Tactic

private def ensureLHSIsMVar (g : MVarId) : MetaM (Expr × Expr × MVarId) :=
  g.withContext do
    let gty ← g.getType'
    let some (_, lhs, rhs) := gty.eq? | throwError "goal must be eq"
    let lhs ← whnfCore lhs
    if lhs.getAppFn.isMVar then
      return (lhs, rhs, g)
    let rhs ← whnfCore rhs
    if rhs.getAppFn.isMVar then
      let [g] ← g.applyConst ``Eq.symm | throwError "failure to apply Eq.symm"
      return (rhs, lhs, g)
    throwError "neither the LHS nor the RHS is a metavariable application"

/--
Replace each expr in `exprs` with the corresponding fvar in `fvars` by using `kabstract`,
and then creates a lambda that closes the fvars.
Throws an error if the result is not type correct.
Returns a lambda, like `mkLambdaFVars fvars e`.
-/
private def mkLambdaGeneralizeFVars (exprs : Array Expr) (fvars : Array Expr) (e : Expr) :
    MetaM Expr := do
  let e ← (exprs.zip fvars).foldrM (init := e) fun (expr, fvar) e => do
    let e' ← kabstract e expr
    pure <| e'.instantiate1 fvar
  unless ← isTypeCorrect e do
    throwError "failed to generalize expression"
  return (← getLCtx).mkBinding (isLambda := true) fvars e

/-- Close `?f a₁ … aₙ = rhs` by assigning `?f := fun x₁ … xₙ => rhs[aᵢ := xᵢ]` — i.e. solve for the
function, not for the value. `rfl` cannot do this: it needs `?f` to already be determined. -/
elab "rflm" : tactic => do
let g ← popMainGoal
  let (lhs, rhs, g) ← ensureLHSIsMVar g
  g.withContext do
    let m := lhs.getAppFn.mvarId!
    if ← m.isDelayedAssigned then
      throwError "metavariable is delayed assigned"
    let args ← lhs.getAppArgs.mapM instantiateMVars
    -- In a telescope for the mvar's own type, so that abstracting each `arg` to the corresponding
    -- `fvar` gives `mkLambdaFVars` a function of the type `?f` was declared at.
    forallBoundedTelescope (← m.getType) args.size fun fvars _ => do
      let rhs ← instantiateMVars rhs
      let rhs' ← mkLambdaGeneralizeFVars args fvars rhs
      unless ← m.checkedAssign rhs' do
        throwError "failed to assign metavariable (due to occurs check or local context mismatches)\n\n\
          Metavariable:{m}\n\
          Value:{indentExpr rhs'}"
    -- Given that that succeeded, now both sides are unified, so Eq.refl must work.
    g.assign (← mkEqRefl rhs)

/-- Unfold every compiler-generated `match_*` auxiliary appearing in the goal. -/
elab "unfold_matches" : tactic =>
  withMainContext do
    let goalType ← getMainTarget
    let consts := goalType.getUsedConstants
    let ms := consts.filter (fun n => n.components.any (·.getString!.startsWith "match_"))
    for m in ms do
      unfoldTarget m
