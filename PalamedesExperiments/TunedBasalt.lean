import Palamedes.Synthesizer
import Palamedes.Synthesizer.CorrectDef
import Palamedes.DeriveTuning
import Palamedes.Stats
import Palamedes.Data.List

/-!
# Probe: a tuned generator at the Basalt shape, via the carrier companion

`derive_tuning` cannot retarget a Basalt-shaped generator directly: `installTuning` keys on the
carrier's `Gen.oneOf`, and the optimizer's `support lhs = support rhs` chain does not typecheck at
an abstract `G`. The doc's costed alternative is a redesign of the proof layer. This probe tests the
cheaper route: **tune at the carrier, then re-project** — which composes only machinery the pipeline
already exercises, *if* three things hold that nothing has exercised before:

* **A.** The `totality` cascade closes `Gen.total` for a *θ-open* tuned term — every weight is an
  opaque `Tuning.weight θ i d` rather than a literal.
* **B.** `extractWitness` projects the resulting witness back to readable generator code — the
  weight lists are no longer literal, so `List.map`/projection steps could get stuck where they
  never did before.
* **C.** The support law crosses to the projected constant at `SPMF` through the witness equation
  (`isSoundAndComplete_of_total`), with the kernel checking the defeq between the extracted body
  and `witness.val.run`.

Each step mirrors what an automated `derive_tuning`-on-Basalt-shape would emit, so a green build of
this file is the go signal for that automation, and the failure point (A/B/C) names the redesign
work if not.

`derive_tuning` now runs this chain automatically for a Basalt-shaped declaration, against the
carrier companion `correct def` emits. This file spells it out by hand, so a break in any single
step (A, B, or C) is localized here rather than surfacing as an opaque `derive_tuning` failure.
-/

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

-- The carrier substrate: a `correct def` (so a `sound_complete` exists to chain) plus its tuning.
correct def genAllTwos : Palamedes.Gen (List Nat) := by
  generator_search (fun xs => isAllTwos xs)

derive_tuning genAllTwos

open Lean Elab Command Meta Term in
run_cmd liftTermElabM do
  let some tunedCI := (← getEnv).find? ``genAllTwos.tuned
    | throwError "probe: genAllTwos.tuned not found"
  withLocalDeclD `θ (mkConst ``Tuning) fun θ => do
    -- The θ-open tuned term — exactly what the automation holds after `buildTuned`.
    let body := tunedCI.value!.beta #[θ]

    -- ── A: totality on the θ-open term ──
    let w ← solveGoalWithTactic
      (← mkAppM ``Palamedes.Gen.total #[body])
      (← `(tactic| totality))
    -- Keep the witness under its pretty statement; the kernel discharges the delta/beta between
    -- `genAllTwos.tuned θ` and the term the tactic actually ran on.
    let tunedApp := mkApp (mkConst ``genAllTwos.tuned) θ
    let stmtA ← instantiateMVars (← mkForallFVars #[θ] (← mkAppM ``Palamedes.Gen.total #[tunedApp]))
    let valueA ← instantiateMVars (← mkLambdaFVars #[θ] w)
    if valueA.hasExprMVar || stmtA.hasExprMVar then
      throwError "probe A: metavariables survived"
    addAndCompile <| .defnDecl {
      name := ``genAllTwos ++ `tunedTotal, levelParams := [], type := stmtA, value := valueA,
      hints := .abbrev, safety := .safe }
    logInfo "probe A ok: totality closed on the θ-open term"

    -- ── B: the projection stays readable ──
    -- Mirror `packageFor`'s `.basalt` branch under a local `G`/instance telescope. Built with
    -- `withLocalDecl` rather than a syntax quotation: a quoted `G` binder carries macro scopes, and
    -- a hygienic binder name cannot be addressed by `(G := …)` at use sites — in the real command
    -- the binders come from the user's declaration, so plain names are the faithful shape.
    let αE ← Term.elabType (← `(List Nat))
    let GTy ← mkArrow (mkSort Level.one) (mkSort Level.one)
    let (extracted, projTy) ← withLocalDecl `G .implicit GTy fun G => do
      let instTy ← mkAppM ``_root_.Gen #[G]
      withLocalDecl `inst .instImplicit instTy fun inst => do
        let tgen ← mkAppOptM ``Subtype.val #[none, none, w]
        let proj ← mkAppOptM ``Palamedes.TGen.run #[some αE, some tgen, some G, none]
        let r ← extractWitness proj
        return (← mkLambdaFVars #[G, inst] r, ← mkForallFVars #[G, inst] (mkApp G αE))
    -- The residue audit's criteria: no casts, no unprojected subtypes, no witness constructors —
    -- in the **data** path. Proof subterms are erased first: the `frequency` side conditions carry
    -- the witness plumbing legitimately, exactly as `PalamedesTest/Extract.lean` exempts the
    -- `._proof_i` auxiliaries the def elaborator abstracts them into. (An emitter going through raw
    -- `addDecl` keeps them inline, which is why the erasure has to be explicit here.)
    let cleaned ← Meta.transform extracted (pre := fun e => do
      if !e.isApp && !e.isLambda && !e.isForall && !e.isLet then return .continue
      if ← Meta.isProof e then return .done (mkConst ``True.intro) else return .continue)
    let forbidden : Array Name :=
      #[``Eq.rec, ``Eq.ndrec, ``Eq.mpr, ``Subtype.val, ``Subtype.mk, ``Palamedes.Gen.pick]
    let bad := cleaned.foldConsts (init := #[]) fun n acc =>
      if forbidden.contains n || (`Palamedes.TGen).isPrefixOf n
          || (`Palamedes.Gen.Total).isPrefixOf n then
        acc.push n
      else acc
    unless bad.isEmpty do
      throwError "probe B: residue {bad} in the projected term's data path{indentExpr extracted}"
    let stmtB ← instantiateMVars (← mkForallFVars #[θ] projTy)
    let valueB ← instantiateMVars (← mkLambdaFVars #[θ] extracted)
    if valueB.hasExprMVar || stmtB.hasExprMVar then
      throwError "probe B: metavariables survived"
    addAndCompile <| .defnDecl {
      name := ``genAllTwos ++ `tunedBasalt, levelParams := [], type := stmtB, value := valueB,
      hints := .abbrev, safety := .safe }
    logInfo m!"probe B ok — projected tuned generator:{indentExpr extracted}"

-- ── C: the law attaches to the *readable* constant, for every θ ──
-- Typechecking this statement is itself the assertion: the kernel verifies
-- `genAllTwos.tunedBasalt θ (G := SPMF)` is definitionally `(genAllTwos.tunedTotal θ).val.run`,
-- i.e. that extraction preserved the term and the witness equation carries the support fact across.
theorem genAllTwos.tunedBasalt_sound_complete (θ : Tuning) :
    IsSoundAndComplete (genAllTwos.tunedBasalt θ (G := SPMF))
      (fun xs => isAllTwos xs = true) :=
  isSoundAndComplete_of_total (genAllTwos.tunedTotal θ).property
    ((genAllTwos.tuned_support θ).trans genAllTwos.sound_complete)

#print axioms genAllTwos.tunedBasalt_sound_complete

-- Smoke: the projected tuned generator *runs* under Basalt's own tooling, weights supplied.
#genstats (draws := 30) (genAllTwos.tunedBasalt genAllTwos.defaults)
