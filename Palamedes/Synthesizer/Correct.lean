/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Synthesizer.FrontEnd
import Palamedes.Laws

/-!
# `@[correct]` — synthesis that names its proofs

`generator_search` proves `support gen = P` on the way to closing its goal. `@[correct]` is what
keeps that proof: it emits `genFoo.sound_complete` as an ordinary theorem about the constant, stated
in **Basalt's** law vocabulary — `IsSoundAndComplete` for a generator declared `G α`,
`IsSomeSoundAndComplete` for one declared `G (Option α)`.

## Why an attribute rather than a command

A theorem about `genFoo` cannot be added while `genFoo` is still being elaborated, and
`applicationTime := .afterCompilation` is precisely the tool for that — the same one `to_additive`
uses to emit declarations derived from the one it is attached to. `Term.getDeclName?` supplies the
name a tactic is elaborating into, so ordering is the only thing an attribute is needed for.

Binder elaboration, auto-bound implicits, universe handling and the `def` syntax itself therefore
stay Lean's, none of which a bespoke command elaborator would have to reimplement. It also composes:
`@[correct]` sits next to any other attribute, and works with `generator_search?`.

The tactic leaves its proofs in `synthesisExt` (see `Synthesizer/FrontEnd.lean`, which documents the
two constraints on what crosses that boundary), and this module reads them back.

**Purely additive.** The generator is exactly the one `generator_search` emits either way; the only
difference is whether the proofs survive.
-/

open Lean Elab Meta Term

namespace Palamedes

/-- `addDecl` a law, after reconciling the independently-built statement and proof.

`isDefEq` rather than `Meta.check` (see `runSynthesisPipeline`), and `instantiateMVars` *after* it,
since `isDefEq` can assign rather than merely compare — an uninstantiated proof reaches the kernel as
"declaration has metavariables", which names the symptom and not the cause.

`xs` are the declaration's binders, which the law is generalized over *after* the reconciliation:
`isDefEq` on the open terms is what the stashed proof's statement was built against, and closing
first would put them out of scope. -/
private def emitLaw (name : Name) (lvls : List Name) (xs : Array Expr) (stmt proof : Expr) :
    MetaM Unit := do
  unless ← isDefEq (← inferType proof) stmt do
    throwError "@[correct]: the proof of `{name}` does not match{indentExpr stmt}\n\
      proof has type{indentExpr (← inferType proof)}"
  let stmt ← instantiateMVars stmt
  let value ← instantiateMVars (← mkExpectedTypeHint proof stmt)
  let stmt ← mkForallFVars xs stmt
  let value ← mkLambdaFVars xs value
  if value.hasExprMVar || stmt.hasExprMVar then
    throwError "@[correct]: `{name}` still has metavariables after instantiation{indentExpr stmt}"
  addDecl <| .thmDecl { name, levelParams := lvls, type := stmt, value }

/-- The declaration applied to its own binders, with the `Gen` monad instantiated at `SPMF`.

A law about a `∀ {G} [Gen G], G α` generator is a statement about its `SPMF` semantics, so `G` and
its instance are *supplied* rather than generalized: the law reads `∀ (lo hi : ℕ),
IsSoundAndComplete (f lo hi) P`, with no vestigial `{G} [Gen G]` that the statement never mentions.
The remaining binders stay, since the predicate may well depend on them.

A `G` that is not a binder — a generator declared directly at some concrete monad — is already at
its own semantics, so there is nothing to instantiate and every binder is kept. -/
private def applyAt (declName : Name) (lvls : List Name) (xs : Array Expr) (G : Expr) :
    MetaM (Expr × Array Expr) := do
  let c := Lean.mkConst declName (lvls.map .param)
  unless G.isFVar do return (mkAppN c xs, xs)
  let spmf := Lean.mkConst ``SPMF [Level.zero]
  let inst ← synthInstance (← mkAppM ``Gen #[spmf])
  let mut args := #[]
  let mut keep := #[]
  for x in xs do
    -- the `[Gen G]` binder is identified by its *type*, since its name is the user's to choose.
    let t ← whnf (← inferType x)
    if x == G then
      args := args.push spmf
    else if t.isAppOfArity ``Gen 1 && t.appArg! == G then
      args := args.push inst
    else
      args := args.push x
      keep := keep.push x
  return (mkAppN c args, keep)

/-- Emit the law for `declName` from its stashed synthesis. Returns its name, for the report — what
was emitted is something to read rather than assume. -/
def emitCorrectLaws (declName : Name) : TermElabM String := do
  let some stash := (synthesisExt.getState (← getEnv)).find? declName
    | throwError "@[correct]: `{declName}` was not synthesized by `generator_search`, so there is \
        no support proof to emit a law from.\n\n\
        `@[correct]` keeps the proof the *tactic* already computed; it does not prove a \
        hand-written generator correct. Declare it as\n\n  \
        @[correct] def {declName} … := by generator_search …\n\n\
        or drop the attribute."
  let some ci := (← getEnv).find? declName
    | throwError "@[correct]: unknown constant {declName}"
  let lvls := ci.levelParams
  forallTelescope ci.type fun xs body => do
    -- Re-open every stashed term at *this* telescope. `declBinders` built them against the binders
    -- in the same order, so the correspondence is positional.
    let pred := stash.pred.beta xs
    let gen := stash.gen.beta xs
    let supportProof := stash.supportProof.beta xs
    let totalWitness? := stash.totalWitness?.map (·.beta xs)
    -- `G` is read off the goal rather than stashed: it is a binder, so the stashed copy would be a
    -- dangling `fvar` here, and the declared type names it anyway.
    let G := body.getAppFn

    -- `f.sound_complete`, stated against the emitted constant rather than the term, so it is a fact
    -- about `f` and not about a copy of its body. The *statement* follows the declared shape, and
    -- both are Basalt's: `IsSoundAndComplete` for a total generator, `IsSomeSoundAndComplete` for a
    -- filtering one.
    match stash.shape with
    | .basalt =>
      let some w := totalWitness?
        | throwError "@[correct]: internal — Basalt shape without a totality witness"
      -- `IsSoundAndComplete (f (G := SPMF)) P`, proved by transferring the pipeline's
      -- `support = P` across the witness equation. No parametricity: both sides are the same
      -- instantiation of the same polymorphic term. `emitLaw`'s `isDefEq` is what reconciles the
      -- statement's `f (G := SPMF)` with the proof's `witness.val.run`, which is the same term
      -- before `extractWitness` performed the projections.
      let hw ← mkAppOptM ``Subtype.property #[none, none, w]
      let proof ← mkAppM ``Palamedes.isSoundAndComplete_of_total #[hw, supportProof]
      let (atSPMF, keep) ← applyAt declName lvls xs G
      let stmt ← mkAppM ``IsSoundAndComplete #[atSPMF, pred]
      emitLaw (declName ++ `sound_complete) lvls keep stmt proof
    | .basaltOption =>
      -- The filtering path. The emitted definition runs the generator at `OptionT SPMF` while the
      -- pipeline proved `support = P` at `SPMF`, so the law is stated with `someSupport` — the
      -- support notion of *that* interpretation — and the bridge between the two is discharged by
      -- `simp` over the combinator twins. That is a fact about this particular generator, not the
      -- global `∀ g, someSupport g = g.support`, which is unprovable.
      let bridgeGoal ← mkEq (← mkAppM ``Palamedes.someSupport #[gen])
        (← mkAppM ``Palamedes.PGen.support #[gen])
      -- `simp` alone suffices for a non-recursive generator: the per-combinator twins fire on both
      -- sides and meet. A *recursive* one does not close, and the reason is not a missing twin.
      -- `X.someSupport_unfold` and `X.support_unfold` both fire, leaving
      -- `unfold_support (fun d x => someSupport (f d x)) … = unfold_support (fun d x => (f d x).support) …`
      -- — equal only if the two step predicates are, which needs congruence under the `unfold_support`
      -- application and then the *step* bridge. The step generator is a nest of conditionals (the
      -- `dite` guarding each constructor choice, plus an `ite` per numeric side condition), and simp
      -- will not case-split them, so it stalls at `someSupport (dite …)` with the twins unreachable
      -- underneath. `repeat' split` exposes the branches; each is then a bare combinator spine the
      -- twins close.
      --
      -- Three details in the script below *weaken* it silently rather than failing:
      --
      -- * `funext d x b` takes **three** binders, not two. `unfold_support`'s predicate is
      --   `fun d x => (f d x).support`, and `support` is itself `α → Prop`, so what `congr 1` leaves
      --   is an equation between 3-ary functions. Introducing only `d x` leaves a lambda equality
      --   that simp discharges only for some generators.
      -- * `(repeat' split)` needs its own parentheses. `;`-sequenced inside a quotation,
      --   `repeat' split; all_goals simp` binds as `repeat' (split; all_goals simp)`, and the
      --   conditionals never get split at all.
      -- * the tail is `try`-guarded because a non-recursive generator is already closed by `simp`
      --   alone, leaving `congr 1` with no goals to work on.
      --
      -- The final `all_goals` handles a **bound scrutinee**, and runs only on what the lines above
      -- left. `split` case-splits a `match` whose scrutinee is in the local context, and after
      -- `someSupport_bind` the interesting one is not: it is bound by an `∃` *inside* the goal, in
      -- `∃ a, P a ∧ someSupport (match a with …) b`, where `split` cannot reach `a` and the twins
      -- sit unreachable under the arms. Taking the `Iff` apart along the structure the two sides
      -- share — they are identical bar `someSupport` vs `support`, so componentwise is exactly
      -- right — introduces `a` as a local, and then `split` applies.
      --
      -- A per-datatype `X.someSupport_cases` beside `X.total_cases` is the obvious alternative and
      -- cannot work: `total_cases` is dispatched by the discriminant's *type* and `apply`d precisely
      -- because matchers are per-elaboration and only defeq, whereas a simp lemma is matched at
      -- `reducible`, so its matcher auxiliary never unifies with the generator's and the lemma never
      -- fires (`rw` fails on it too). The obstacle is tactical rather than per-datatype, and so is
      -- this fix: nothing here mentions a datatype, so a type declared in a test file gets it free.
      let bridge ←
        try
          solveGoalWithTactic bridgeGoal
            (← `(tactic|
              (simp
               try (congr 1; funext d x b; (repeat' split); all_goals simp)
               all_goals (try (
                 (repeat' (first
                   | apply or_congr
                   | apply and_congr
                   | apply exists_congr
                   | intro _)) <;> (repeat' split) <;> simp)))))
        catch e =>
          -- Deliberately names no single cause: a missing twin and a control-flow shape the script
          -- cannot case-split produce the same unsolved goal, and a confidently wrong diagnosis
          -- sends the reader to the wrong file.
          throwError "@[correct]: could not relate this generator's `someSupport` to its \
            `support`, so the filtering law cannot be stated. The unsolved goal is below.\n\n\
            Two things commonly leave one: a combinator with no `someSupport` twin (add it beside \
            the `support_` lemma — see `Data/Nat.lean` for the pattern), or a step generator whose \
            control flow the bridge could not case-split to reach the twins underneath. Compare the \
            two sides of the goal: if they differ only inside a `match` or an `if`, it is the \
            second.\n{e.toMessageData}"
      let hsome ← mkAppM ``Eq.trans #[bridge, supportProof]
      let proof ← mkAppM ``Palamedes.isSomeSoundAndComplete_of_someSupport #[hsome]
      let (atSPMF, keep) ← applyAt declName lvls xs G
      let stmt ← mkAppM ``Palamedes.IsSomeSoundAndComplete #[atSPMF, pred]
      emitLaw (declName ++ `sound_complete) lvls keep stmt proof

    -- There is no `f.total` companion, at either shape: `PGen.total` is a statement about the
    -- pipeline's internal carrier, and a Basalt-shaped generator has no `Fail` to be free of. Its
    -- totality is already the content of its declared type, which is why `G α` is an error for a
    -- generator that filters rather than a shape carrying extra evidence.
    return "sound_complete"

initialize registerBuiltinAttribute {
  name := `correct
  descr := "keep the support proof `generator_search` computed, as named theorems about this \
    declaration"
  -- The laws are *about* the constant, so they cannot be added until it exists.
  applicationTime := .afterCompilation
  add := fun declName _ _ => do
    let emitted ← MetaM.run' <| TermElabM.run' <| emitCorrectLaws declName
    logInfo m!"@[correct] {declName}: emitted {emitted}"
}

end Palamedes
