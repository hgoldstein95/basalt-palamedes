/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Synthesizer.CGeneratorSearch

/-!
# Stage-1 Failure Diagnosis

`diagnoseSearchFailure` runs only after `cgenerator_search` has failed: it replays the search's own
normalization stages one at a time and names the gate that declined, so the error is a statement
about the predicate rather than Aesop's uniform "made no progress".
-/

open Lean Elab Meta Tactic

namespace Palamedes

/-- Run `tac` against `goal`, returning the remaining goals, or `none` — with the elaboration state
restored — if it throws. Interrupts and exhaustion are rethrown: they are not evidence about the
goal. -/
private def tryTac (goal : MVarId) (tac : TSyntax `tactic) : TermElabM (Option (List MVarId)) := do
  let s ← saveState
  try
    return some (← Tactic.run goal (Tactic.evalTactic tac))
  catch e =>
    if e.isInterrupt || e.isMaxHeartbeat || e.isMaxRecDepth then throw e
    s.restore
    return none

/-- Reference a registered constant from a quotation built at diagnosis time, immune to whatever
the caller has `open`. Same move as `normalize_and_apply_unfold`. -/
private def root (n : Name) : Ident := mkIdent (`_root_ ++ n)

private def searchGoal (α pred : Expr) : TermElabM MVarId :=
  return (← mkFreshExprMVar (mkAppN (.const ``Palamedes.CorrectGen []) #[α, pred])).mvarId!

private def isEqGoal (g : MVarId) : MetaM Bool :=
  g.withContext do return (← instantiateMVars (← g.getType)).isAppOf ``Eq

/-- The `s_unfold` subgoal asking for the per-step generator: `(b : β) → (s : σ) → CorrectGen _`. -/
private def isStepGenGoal (g : MVarId) : MetaM Bool :=
  g.withContext do
    forallTelescopeReducing (← instantiateMVars (← g.getType)) fun _ body =>
      return body.isAppOf ``Palamedes.CorrectGen

/-- Const-headed applications in `e` that take `a` as a direct argument, in traversal order.
Logical connectives are skipped: the interesting application is the predicate's own function. -/
private partial def appsMentioning (a : Expr) (e : Expr) : Array (Name × Array Expr) :=
  go e #[]
where
  go (e : Expr) (acc : Array (Name × Array Expr)) : Array (Name × Array Expr) :=
    match e with
    | .mdata _ b => go b acc
    | .app .. =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      let skip : List Name := [``Eq, ``Ne, ``Iff, ``And, ``Or, ``Not, ``decide]
      let acc :=
        match fn with
        | .const n _ => if !skip.contains n && args.contains a then acc.push (n, args) else acc
        | _ => acc
      args.foldl (fun acc x => go x acc) (go fn acc)
    | .lam _ _ b _ | .forallE _ _ b _ => go b acc
    | .letE _ _ v b _ => go b (go v acc)
    | _ => acc

/-- Whether `fn` is defined by recursion over `ty`. A heuristic — structural recursion elaborates
to `ty.brecOn`/`ty.rec`, well-founded recursion to `WellFounded.fix` — used only to phrase a
failure-path message. -/
private def isRecursiveOver (fn ty : Name) : CoreM Bool := do
  let some ci := (← getEnv).find? fn | return false
  let some v := ci.value? | return false
  return v.getUsedConstants.any fun n =>
    n == ty ++ `rec || n == ty ++ `brecOn || n == ``WellFounded.fix

/-- Where the generation target `a` sits in `fn args`: its 1-based position among `fn`'s explicit
arguments, and the number of explicit arguments after it. -/
private def targetPosition (fn : Name) (args : Array Expr) (a : Expr) :
    MetaM (Option (Nat × Nat)) := do
  let some ci := (← getEnv).find? fn | return none
  forallBoundedTelescope ci.type args.size fun params _ => do
    let mut pos := 0
    let mut expl := 0
    let mut after := 0
    for i in [0:args.size] do
      let isExpl ← match params[i]? with
        | some p => do pure (← p.fvarId!.getDecl).binderInfo.isExplicit
        | none => pure true
      if isExpl then
        expl := expl + 1
        if args[i]! == a then
          pos := expl
        else if pos != 0 then
          after := after + 1
    if pos == 0 then return none
    return some (pos, after)

/-- The message for a refused coercion, refined by how the predicate arranges the arguments of its
recursive function — the contract (`f t`, indices tupled into at most one trailing argument) is
otherwise written nowhere a user will look. `merged` says the `∧`-merge split the predicate into
several goals, of which this replay names the first that refused — not necessarily the pipeline's
actual point of failure. -/
private def coercionRefused (entry : UnfoldStrategy) (pred : Expr) (merged : Bool) :
    MetaM MessageData := do
  let base := m!"Unfold synthesis for `{entry.typeName}` stopped at the coercion: \
    `{entry.coerce}` could not rewrite this predicate into a `{entry.fold}`."
  let caveat :=
    if merged then
      m!"\nThe `∧`-merge split this predicate, and this names the first goal whose coercion \
        refused; in the full pipeline a refused coercion still falls through to the conversion \
        step, so the culprit may be a different conjunct — or the merge itself."
    else
      m!""
  let hint? ← lambdaTelescope pred fun xs body => do
    let some a := xs[0]? | return none
    let apps := appsMentioning a body
    let mut chosen := none
    for (fn, args) in apps do
      if ← isRecursiveOver fn entry.typeName then
        chosen := some (fn, args)
        break
    let some (fn, args) := chosen <|> apps[0]? | return none
    let some (pos, after) ← targetPosition fn args a | return none
    if pos != 1 then
      return some m!"The generation target is `{fn}`'s explicit argument {pos}; the coercion \
        unifies the `{entry.typeName}`-typed argument first, so spell the recursion with that \
        argument first and any indices after it."
    if after ≥ 2 then
      return some m!"`{fn}` takes {after} curried arguments after the generation target, and the \
        coercion handles at most one — tuple the indices into a single trailing argument \
        (`{fn} t (i, j)`) and match on the tuple in the defining equations."
    return some m!"The argument arrangement is fine (target first, {after} trailing), so the \
      refusal is about `{fn}`'s defining equations: they could not be read back as a fold \
      algebra over `{entry.typeName}`."
  match hint? with
  | some h => return m!"{base}\n{h}{caveat}"
  | none => return m!"{base}{caveat}"

private def conversionRefused (entry : UnfoldStrategy) (goal : Format) : MessageData :=
  let lemmas := MessageData.andList (entry.convert.toList.map (m!"`{·}`"))
  m!"Unfold synthesis for `{entry.typeName}` got past the coercion — the predicate reads as a \
    `{entry.fold}` — but converting that fold to the `accuM` normal form refused: none of \
    {lemmas} matched. The conversions expect each recursive arm as \
    `condition && accumulated results` (a bare accumulator and `&&` reassociation are handled); \
    an arm outside that form has no conversion, and `unfold_strategy_convert` is how a \
    hand-written one is registered. The conversion was attempted against:{indentD goal}"

/-- Diagnose against the unfold pipeline for `entry`, the strategy registered for the goal's
element type. The authoritative probe is the entry's own `norm_for_unfold`, verbatim; only when it
refuses is it replayed one stage at a time to name the gate. -/
private def diagnoseUnfold (entry : UnfoldStrategy) (α pred : Expr) :
    TermElabM (Option MessageData) := do
  let g ← searchGoal α pred
  let some gs ← tryTac g (← `(tactic| goal_is_eq_or_and))
    | return some m!"`{entry.typeName}` is registered for unfold synthesis, but the unfold rule \
        fires only on predicates shaped `fun x => _ = _` or `fun x => _ ∧ _` — this predicate is \
        neither, so the unfold path was never entered. (Other rules may still apply to such \
        shapes; none closed this goal.)"
  let [g] := gs | return none
  -- Enter the entry's arm exactly as `normalize_and_apply_unfold` does.
  let sUnfold : Lean.Term := root entry.sUnfold
  let some gs ← tryTac g (← `(tactic| (apply Palamedes.PGen.CorrectGen.convert ?pf ?arg
                                       case' pf => try accu_simp
                                       case' arg => apply $sUnfold:term _)))
    | return none
  let some pf ← gs.findM? (liftM <| isEqGoal ·) | return none
  let fold := root entry.fold
  let coerce : Lean.Term := root entry.coerce
  let merge : Lean.Term := root entry.merge
  let convs : Syntax.TSepArray `term "," := .ofElems (entry.convert.map (root · : Name → Lean.Term))
  let norm ← match entry.cond with
    | some c => `(tactic| norm_for_unfold $fold $coerce mergeVia $merge
                    convertVia [$convs,*] condVia $(root c))
    | none => `(tactic| norm_for_unfold $fold $coerce mergeVia $merge convertVia [$convs,*])
  let preNorm ← saveState
  let mut degenerateStep : Option Format := none
  match ← tryTac pf norm with
  | some [] =>
    -- The normalization closed, which is what the pipeline's `case pf =>` demands of it. If it
    -- also *determined* the per-step generator, the search genuinely failed below the unfold; a
    -- step goal with metavariables or a `sorry` left in it means the iff closed only formally —
    -- a fold algebra was never actually read off the predicate (a refused coercion discharge
    -- elaborates to `sorry`) — and the coercion is what deserves the blame, so fall through to
    -- the stagewise replay.
    let mut step? : Option (Format × Bool) := none
    for s in gs do
      unless ← s.isAssigned do
        if ← isStepGenGoal s then
          let ty ← s.withContext do instantiateMVars (← s.getType)
          let determined := !ty.hasExprMVar && !ty.hasSorry
          let fmt ← s.withContext do ppGoal s
          step? := some (fmt, determined)
          break
    match step? with
    | none => return none
    | some (stepGoal, true) =>
      return some m!"The `{entry.typeName}` unfold rule itself fires on this predicate — \
        coercion and `accuM` conversion both succeed — so the search failed below the unfold, \
        while synthesizing its per-step generator:{indentD stepGoal}\nThe usual causes are a \
        constructor field whose type has no synthesis rules, or a step condition no leaf rule \
        closes."
    | some (stepGoal, false) =>
      degenerateStep := some stepGoal
      preNorm.restore
  | some _ =>
    -- Ran to completion but left goals open, which `case pf =>` counts as failure.
    preNorm.restore
  | none => pure ()
  -- The normalization refused (or closed without content); replay it one stage at a time to name
  -- the gate.
  let some pfGoals ← tryTac pf (← `(tactic| (preprocess
                                             repeat' (rw_merge $merge))))
    | return none
  let mut alts : Array (TSyntax ``Lean.Parser.Tactic.tacticSeq) := #[]
  for l in entry.convert do
    alts := alts.push (← `(tacticSeq| accu_convert_one $(root l):term))
  if let some c := entry.cond then
    alts := alts.push (← `(tacticSeq| rw_true_and; rw [← $(root c):term]; (try aesop); done))
  let convertStep ← `(tactic| (first $[| $alts]*))
  for h in pfGoals do
    let alreadyFold := (← tryTac h (← `(tactic| goal_is_not_fold $fold))).isNone
    let coerced ←
      if alreadyFold then
        pure (some [h])
      else if let some hs ← tryTac h (← `(tactic| coerce_fold_strict $fold $coerce)) then
        pure (some hs)
      else
        tryTac h (← `(tactic| (simp; coerce_fold_strict $fold $coerce)))
    let some hs := coerced
      | return some (← coercionRefused entry pred (pfGoals.length > 1))
    for h' in hs do
      if (← tryTac h' convertStep).isNone then
        return some (conversionRefused entry (← h'.withContext do ppGoal h'))
  match degenerateStep with
  | some stepGoal =>
    return some m!"Unfold synthesis for `{entry.typeName}` appeared to normalize, but without \
      determining the per-step generator — its goal still contains metavariables or `sorry`:\
      {indentD stepGoal}\nThis usually means the predicate is not spelled as a fold the \
      coercion can read off."
  | none => return none

/-- Diagnose a predicate whose element type has no `unfold_strategy` entry: either a recursion over
a datatype nothing registered, or a leaf-shaped predicate no rule matched — where the useful fact
is what the rules were matched *against*. -/
private def diagnoseBare (α pred : Expr) : TermElabM (Option MessageData) := do
  if let .const tyName _ := α.getAppFn then
    -- Leaf types are handled by enumerated rules, not by unfold synthesis; suggesting
    -- `derive_palamedes Nat` would be worse than saying nothing.
    let leafTypes : List Name := [``Nat, ``Bool, ``Int, ``Char, ``String]
    if !leafTypes.contains tyName && ((← getEnv).find? tyName).any (·.isInductive) then
      let rec? ← lambdaTelescope pred fun xs body => do
        let some a := xs[0]? | return none
        (appsMentioning a body).findM? fun (fn, _) => isRecursiveOver fn tyName
      if let some (fn, _) := rec? then
        -- `isRecursiveOver` cannot attribute a `WellFounded.fix` to a measure, so the message
        -- asserts only the registry fact and leaves `fn`'s recursion unclaimed.
        return some m!"`{tyName}` has no `unfold_strategy` entry, so the unfold rule could not \
          fire on `{fn}`. If `{tyName}` is a plain recursive datatype, \
          `derive_palamedes {tyName}` registers everything unfold synthesis needs."
  -- Replay the shared normalization every leaf rule sees the predicate through.
  let g ← searchGoal α pred
  let some gs ← tryTac g (← `(tactic| (apply Palamedes.PGen.CorrectGen.convert ?pf ?arg
                                       case' pf => unfold_matches; try accu_simp)))
    | return none
  let some pf ← gs.findM? (liftM <| isEqGoal ·) | return none
  let normalized? ← pf.withContext do
    let some (_, _, rhs) := (← instantiateMVars (← pf.getType)).eq? | pure (none : Option Expr)
    pure (some rhs)
  let some normalized := normalized? | return none
  if (← instantiateMVars pred) != normalized then
    return some m!"No search rule matched. The normalizing rules were tried \
      against{indentD (← ppExpr normalized)}\nrather than the spelling as written (rules that \
      apply directly saw the original) — if that shape is not the one you meant to expose, \
      respell the predicate so normalization preserves it."
  return some m!"No search rule matched this predicate, and the search's shared normalization \
    does not change it — the spelling as written is exactly what every rule was tried against."

private inductive SplitProbe where
  | notDisjunction
  | bothClose
  | fails (side : String) (disjunct : Expr)

/-- `s_pick` splits a top-level disjunction into one search per disjunct, so a failing disjunction
is diagnosed by finding which disjunct the search cannot close on its own. -/
private def probeDisjunction (α pred : Expr) : TermElabM SplitProbe := do
  let parts? ← lambdaBoundedTelescope pred 1 fun xs body => do
    let some a := xs[0]? | return (none : Option (Expr × Expr))
    let some (l, r) := body.app2? ``Or | return none
    return some (← mkLambdaFVars #[a] l, ← mkLambdaFVars #[a] r)
  let some (l, r) := parts? | return .notDisjunction
  for (side, p) in [("left", l), ("right", r)] do
    let g ← searchGoal α p
    match ← tryTac g (← `(tactic| cgenerator_search)) with
    | some [] => pure ()
    | _ => return .fails side p
  return .bothClose

/-- The dispatch behind `diagnoseSearchFailure`; `fuel` bounds the recursion into disjuncts. -/
private partial def diagnoseCore (α pred : Expr) (fuel : Nat) : TermElabM (Option MessageData) := do
  if fuel > 0 then
    match ← probeDisjunction α pred with
    | .fails side p =>
      let head := m!"`s_pick` splits the disjunction, and its {side} disjunct\
        {indentD (← ppExpr p)}\nis the one the search cannot close."
      let sub? ← diagnoseCore α p (fuel - 1)
      return some (match sub? with
        | some sub => m!"{head}\n\n{sub}"
        | none => head)
    | .bothClose =>
      return some m!"Each disjunct of this predicate synthesizes on its own, so the failure is in \
        splitting the disjunction itself (`s_pick` and its normalization) — or the combined \
        search exhausted a budget the separate searches did not."
    | .notDisjunction => pure ()
  match (unfoldStrategies (← getEnv)).find? (fun e => α.getAppFn.isConstOf e.typeName) with
  | some entry => diagnoseUnfold entry α pred
  | none => diagnoseBare α pred

/-- Diagnose a failed `cgenerator_search` over `pred : α → Prop`: replay the search's own gates on
cheap evidence and name the one that declined, or `none` when no specific story fits. Runs only on
the failure path, so nothing here is paid for on success.

The model is stage 4's `diagnoseNoWitness`: an actionable statement about the predicate, not a dump
of the search's internals. All probing happens inside `withoutModifyingState`, and every message is
rendered eagerly so it survives the rollback. -/
def diagnoseSearchFailure (α pred : Expr) : TermElabM (Option MessageData) := do
  try
    withoutModifyingState do
      diagnoseCore α pred 4
  catch e =>
    -- The diagnosis exhausting its own budget must not replace the search's real error.
    if e.isInterrupt then throw e
    return none

end Palamedes
