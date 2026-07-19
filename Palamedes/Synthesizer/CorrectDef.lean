import Palamedes.Synthesizer.FrontEnd
import Palamedes.Laws

/-!
# `correct def` — synthesis that names its proofs

`generator_search` is a *tactic*: it holds an `MVarId` and closes it with `closeMainGoal`, and never
learns the name of the declaration it is elaborating into. So it cannot emit a theorem *about* that
declaration, however many proofs it computed along the way — which is why the synthesizer proved
`support = P` and discarded it. `derive_tuning` can emit `tuned_support` only because it is a
command and reads `declName` off its own syntax.

`correct def` closes that gap by owning the elaboration: it runs the shared pipeline, `addDecl`s the
generator, and then `addDecl`s the laws against the now-existing constant, holding the proofs as
ordinary local values in between. There is no environment extension and no cross-command state.

It is **purely additive** — the generator it emits is exactly the one `generator_search` would have
produced. The only difference is that the proofs survive.
-/

open Lean Elab Command Meta Term

namespace Palamedes

/-- `correct def f binders* : τ := by generator_search P` synthesizes `f` exactly as
`generator_search` would, and additionally emits the laws the pipeline proved on the way. Which laws
depends on the declared shape — the same dispatch the tactic does:

* `f [Gen G] : G α` — `f.sound_complete : IsSoundAndComplete f P`, in **Basalt's** vocabulary, about
  `f` at `SPMF`. This is the case the exercise exists for: a Basalt-shaped generator carrying a
  named law.
* `f : Palamedes.Gen α` — `f.sound_complete : f.support = P`, at the synthesis-internal carrier,
  plus `f.total : Gen.total f` when the generator is assume-free. `total` is `Type`-valued, so it
  *is* the failure-free generator; `f.total.val.run` is a Basalt-shaped `∀ {G} [Gen G], G α`.
* `f [Gen G] : G (Option α)` — `f.sound_complete : IsSomeSoundAndComplete f P`, the filtering
  path's law: the `some` values it produces are exactly `P`. It says nothing about `none`, because
  the support of a generator that can fail contains `none` and that carries no information.

Binders are what let the first case exist at all — `[Gen G]` cannot be written otherwise. The laws
are generalized over the value binders (`∀ lo hi, …`) but *not* over `G`, which the Basalt law
supplies as `SPMF`.

Laws are discoverable by naming convention (`f.sound_complete`), not via a registry, and the command
**reports what it emitted** — so a missing law is something you read rather than assume. -/
syntax (name := correctDef)
  "correct" "def" ident (ppSpace bracketedBinder)* ":" term ":=" "by" "generator_search" term
  : command

/-- `addDecl` a law, after reconciling the independently-built statement and proof.

`isDefEq` rather than `Meta.check` (see `runSynthesisPipeline`), and `instantiateMVars` *after* it,
since `isDefEq` can assign rather than merely compare — an uninstantiated proof reaches the kernel as
"declaration has metavariables", which names the symptom and not the cause.

`xs` are the declaration's binders, which the law is generalized over *after* the reconciliation:
`isDefEq` on the open terms is what the mvars in the pipeline's proof were created against, and
closing first would put them out of scope. -/
private def emitLaw (name : Name) (xs : Array Expr) (stmt proof : Expr) : TermElabM Unit := do
  unless ← isDefEq (← inferType proof) stmt do
    throwError "correct def: the proof of `{name}` does not match{indentExpr stmt}\n\
      proof has type{indentExpr (← inferType proof)}"
  let stmt ← instantiateMVars stmt
  let value ← instantiateMVars (← mkExpectedTypeHint proof stmt)
  let stmt ← mkForallFVars xs stmt
  let value ← mkLambdaFVars xs value
  if value.hasExprMVar || stmt.hasExprMVar then
    throwError "correct def: `{name}` still has metavariables after instantiation{indentExpr stmt}"
  addDecl <| .thmDecl { name, levelParams := [], type := stmt, value }

/-- The declaration applied to its own binders, and — for a Basalt-shaped generator — the same thing
with the `Gen` monad instantiated at `SPMF`.

A law about a `∀ {G} [Gen G], G α` generator is a statement about its `SPMF` semantics, so `G` and
its instance are *supplied* rather than generalized: the law reads `∀ (lo hi : ℕ),
IsSoundAndComplete (f lo hi) P`, with no vestigial `{G} [Gen G]` that the statement never mentions.
The remaining binders stay, since the predicate may well depend on them. -/
private def applyAt (declName : Name) (xs : Array Expr) (G? : Option Expr) :
    TermElabM (Expr × Array Expr) := do
  let some G := G? | return (mkAppN (mkConst declName) xs, xs)
  unless G.isFVar do return (mkAppN (mkConst declName) xs, xs)
  let spmf := Lean.mkConst ``SPMF [Level.zero]
  let inst ← synthInstance (← mkAppM ``_root_.Gen #[spmf])
  let mut args := #[]
  let mut keep := #[]
  for x in xs do
    -- the `[Gen G]` binder is identified by its *type*, since its name is the user's to choose.
    let t ← whnf (← inferType x)
    if x == G then
      args := args.push spmf
    else if t.isAppOfArity ``_root_.Gen 1 && t.appArg! == G then
      args := args.push inst
    else
      args := args.push x
      keep := keep.push x
  return (mkAppN (mkConst declName) args, keep)

@[command_elab correctDef]
def elabCorrectDef : CommandElab := fun stx => do
  match stx with
  | `(command| correct def $name:ident $bs:bracketedBinder* : $ty:term
        := by generator_search $pred:term) => do
    let declName := (← getCurrNamespace) ++ name.getId
    -- Everything happens inside the binders' local context. The laws have to be built there too —
    -- their statements mention the binders (`f lo hi`), and the pipeline's proof mvars were created
    -- against that context — so the generator is added *inside* this block rather than after it.
    let emitted ← liftTermElabM <| Term.withAutoBoundImplicit <|
      Term.elabBinders bs fun xs => do
      let tyE ← Term.elabTerm ty none
      Term.synthesizeSyntheticMVarsNoPostponing
      let tyE ← instantiateMVars tyE
      -- `[Gen G]` with `G` never bound explicitly is the idiomatic Basalt spelling, so the auto-bound
      -- implicits are collected here and become the declaration's leading binders.
      let xs ← Term.addAutoBoundImplicits xs none
      -- Same dispatch as the tactic: the declared type chooses the shape, and `Option` is what
      -- `allow_partial` used to say.
      let (target, predE) ← classifyGoal tyE pred
      let α := target.elemType
      let res ← runSynthesisPipeline α predE true (palamedes.debug.get (← getOptions))
      -- The pipeline creates mvars of its own (one per `solveGoalWithTactic` goal), so drain the
      -- synthetic queue *after* it runs, not just after elaborating the predicate.
      Term.synthesizeSyntheticMVarsNoPostponing
      let genVal ← instantiateMVars (← packageFor target res (fun msg => logWarning msg))
      let resGen ← instantiateMVars res.gen
      let supportProof ← instantiateMVars res.supportProof
      let totalWitness? ← res.totalWitness?.mapM instantiateMVars
      let predE ← instantiateMVars predE

      -- The generator itself, compiled: `#genstats`/`#eval` run these.
      -- `instantiateMVars` *after* the abstraction, not before: `mkForallFVars`/`mkLambdaFVars` pull
      -- in each binder's type from the local context, and those are exactly what still hold the
      -- universe mvar `classifyGoal` assigned when it pinned `G : Type → Type`. Instantiating only
      -- `tyE`/`genVal` leaves it, and the kernel then reports "declaration has metavariables" on a
      -- term that prints without a single visible `?m`.
      let genTy ← instantiateMVars (← mkForallFVars xs tyE)
      let genBody ← instantiateMVars (← mkLambdaFVars xs genVal)
      if genBody.hasExprMVar || genBody.hasLevelMVar || genTy.hasExprMVar
          || genTy.hasLevelMVar then
        throwError "correct def: the generator still has metavariables after \
          instantiation{indentExpr genTy}"
      addAndCompile <| .defnDecl {
        name := declName, levelParams := [], type := genTy, value := genBody
        hints := .abbrev, safety := .safe }

      let mut emitted := #["(generator)"]

      -- `f.sound_complete`, stated against the emitted constant rather than the term, so it is a
      -- fact about `f` and not about a copy of its body. The *statement* follows the declared shape:
      -- a Basalt-shaped generator gets Basalt's `IsSoundAndComplete`, which is the point of the
      -- exercise; the synthesis-internal carrier keeps the Palamedes-level `support = P`.
      match target with
      | .palamedes _ =>
        let (declC, keep) ← applyAt declName xs none
        let stmt ← mkEq (← mkAppM ``Palamedes.Gen.support #[declC]) predE
        emitLaw (declName ++ `sound_complete) keep stmt supportProof
      | .basalt G _ =>
        let some w := totalWitness?
          | throwError "correct def: internal — Basalt shape without witness"
        -- `IsSoundAndComplete (f (G := SPMF)) P`, proved by transferring the pipeline's
        -- `support = P` across the witness equation. No parametricity: both sides are the same
        -- instantiation of the same polymorphic term. `emitLaw`'s `isDefEq` is what reconciles the
        -- statement's `f (G := SPMF)` with the proof's `witness.val.run`, which is the same term
        -- before `extractWitness` performed the projections.
        let hw ← mkAppOptM ``Subtype.property #[none, none, w]
        let proof ← mkAppM ``Palamedes.isSoundAndComplete_of_total #[hw, supportProof]
        let (atSPMF, keep) ← applyAt declName xs (some G)
        let stmt ← mkAppM ``IsSoundAndComplete #[atSPMF, predE]
        emitLaw (declName ++ `sound_complete) keep stmt proof
      | .basaltOption G _ =>
        -- The filtering path. The emitted definition runs the generator at `OptionT SPMF` while the
        -- pipeline proved `support = P` at `SPMF`, so the law is stated with `someSupport` — the
        -- support notion of *that* interpretation — and the bridge between the two is discharged by
        -- `simp` over the combinator twins. That is a fact about this particular generator, not the
        -- global `∀ g, someSupport g = g.support` of PLAN §5, which remains unprovable.
        let bridgeGoal ← mkEq (← mkAppM ``Palamedes.someSupport #[resGen])
          (← mkAppM ``Palamedes.Gen.support #[resGen])
        let bridge ←
          try
            solveGoalWithTactic bridgeGoal (← `(tactic| simp))
          catch e =>
            throwError "correct def: could not relate this generator's `someSupport` to its \
              `support`. Every combinator it uses needs a `someSupport` twin; a missing one shows \
              up here as an unsolved goal.\n{e.toMessageData}"
        let hsome ← mkAppM ``Eq.trans #[bridge, supportProof]
        let proof ← mkAppM ``Palamedes.isSomeSoundAndComplete_of_someSupport #[hsome]
        let (atSPMF, keep) ← applyAt declName xs (some G)
        let stmt ← mkAppM ``Palamedes.IsSomeSoundAndComplete #[atSPMF, predE]
        emitLaw (declName ++ `sound_complete) keep stmt proof
      emitted := emitted.push "sound_complete"

      -- `f.total` only applies to the synthesis-internal carrier: `Gen.total` is a statement about a
      -- `Palamedes.Gen`, and a Basalt-shaped generator has no `Fail` to be free of — its totality is
      -- already the content of its type.
      match target, totalWitness? with
      | .palamedes _, some w =>
        let (declC, keep) ← applyAt declName xs none
        let stmt ← mkAppM ``Palamedes.Gen.total #[declC]
        unless ← isDefEq (← inferType w) stmt do
          throwError "correct def: the totality witness does not match{indentExpr stmt}"
        let stmt ← instantiateMVars stmt
        let value ← instantiateMVars (← mkExpectedTypeHint w stmt)
        let stmt ← mkForallFVars keep stmt
        let value ← mkLambdaFVars keep value
        if value.hasExprMVar || stmt.hasExprMVar then
          throwError "correct def: `total` still has metavariables after instantiation"
        addAndCompile <| .defnDecl {
          name := declName ++ `total, levelParams := [], type := stmt, value
          hints := .abbrev, safety := .safe }
        emitted := emitted.push "total"
      | _, _ => pure ()

      return emitted

    let emittedStr := String.intercalate ", " emitted.toList
    logInfo m!"correct def {name.getId}: emitted {emittedStr}"
  | _ => throwUnsupportedSyntax

end Palamedes
