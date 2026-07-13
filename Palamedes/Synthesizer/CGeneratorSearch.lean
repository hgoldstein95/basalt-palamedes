import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.RuleSets
import Palamedes.CaseSplit
import Palamedes.Total
import Palamedes.Data.List
import Palamedes.Data.Stack.Stack
import Palamedes.Data.STLC.Term
import Palamedes.Data.STLC.Ty
import Palamedes.Data.STLC.Context
import Palamedes.Data.Tree
import Palamedes.Data.Unit
import Palamedes.Data.Nat
import Palamedes.Data.Bool
import Palamedes.Data.Color
import Palamedes.Data.Tuple
import Palamedes.Util

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

section Guards

macro "goal_is_mergeable" : tactic =>
  `(tactic|
    first
      | change _ ↔ _ ∧ _
      | change _ ↔ (_ && _) = true)

open Lean Lean.Elab.Tactic in
elab "goal_is_not_fold" f:ident : tactic => do
  let fName ← resolveGlobalConstNoOverload f
  let tgt ← instantiateMVars (← getMainTarget)
  match tgt.getAppFnArgs with
  | (``Iff, #[_, b]) =>
    match b.eq? with
    | some (_, lhs, _) =>
      if lhs.getAppFn.isConstOf fName then
        throwError "goal_is_not_fold: predicate is already a fold"
    | none => pure ()
  | _ => pure ()

macro "goal_is_eq" : tactic =>
  `(tactic| guard_target = CorrectGen (fun _ => _ = _))

macro "goal_is_eq_or_and" : tactic =>
  `(tactic|
    first
      | goal_is_eq
      | guard_target = CorrectGen (fun _ => _ ∧ _))


end Guards

section Simplifiers

macro "simp_bexp" : tactic => `(tactic|
  try simp only [bind, Option.bind, pure, Option.some_inj, ← Bool.eq_iff_iff])

macro "accu_simp" : tactic =>
  `(tactic| simp [guard, Option.bind_eq_some_iff, -beq_iff_eq, -Bool.true_and, *])

macro "coerce_discharge" : tactic =>
  `(tactic|
    first
      | rflm
      | (intros; simp_all [- Bool.not_eq_eq_eq_not, -beq_iff_eq]; rflm)
      | aesop)

end Simplifiers

section Normalizers

macro "preprocess" : tactic =>
  `(tactic|
    (funext
     try simp only [eq_iff_iff]))

section Merges

macro "rw_merge" m:term : tactic =>
  `(tactic|
    (goal_is_mergeable
     rw [← $m]
     apply and_congr))

/-
  The fold_accu_cond lemmas expect the bodies of the folds they operate on to be
  in a particular normal form, i.e. `condition && acc` for lists and `condition && accL && accR`
  for trees, in both arms of the conditional. Sometimes, however, the arm of the conditional
  will just look like `acc`, and not be obviously in this normal form. We can
  massage it into the normal form to apply the lemma however by converting
  the `acc` into `true && acc`, which is what these rewrite macros do.
-/
macro "rw_true_and_list" : tactic =>
  `(tactic| conv =>
        pattern fun _ _ _ => _
        repeat intro
        try conv =>
          arg 2; fail_if_success {guard_target = _ && _}; refine (Bool.and_true ..).symm.trans (Bool.and_comm ..)
        try conv =>
          arg 3; fail_if_success {guard_target = _ && _}; refine (Bool.and_true ..).symm.trans (Bool.and_comm ..))

macro "rw_true_and_tree" : tactic =>
  `(tactic| conv =>
        pattern fun _ _ _ _ => _
        intro accL _ accR _
        try conv =>
          arg 2; fail_if_success {guard_target = _ && _ && _}; apply (Bool.and_true ..).symm.trans ((Bool.and_comm ..).symm.trans (Bool.and_assoc ..).symm)
        try conv =>
          arg 3; fail_if_success {guard_target = _ && _ && _}; apply (Bool.and_true ..).symm.trans ((Bool.and_comm ..).symm.trans (Bool.and_assoc ..).symm))

macro "rw_true_and" : tactic =>
  `(tactic| first | rw_true_and_tree | rw_true_and_list | skip)

end Merges

section Coercions

macro "coerce_fold" fh:ident co:term:max : tactic =>
  `(tactic|
    (first
      | goal_is_not_fold $fh; conv => rhs; lhs; apply $co (by coerce_discharge) (by coerce_discharge) (by coerce_discharge) (by coerce_discharge)
      | goal_is_not_fold $fh; conv => rhs; lhs; apply $co (by coerce_discharge) (by coerce_discharge) (by coerce_discharge)
      | goal_is_not_fold $fh; conv => rhs; lhs; apply $co (by coerce_discharge) (by coerce_discharge)
      | goal_is_not_fold $fh; conv => rhs; lhs; apply congrFun; apply $co (by coerce_discharge) (by coerce_discharge) (by coerce_discharge) (by coerce_discharge)
      | goal_is_not_fold $fh; conv => rhs; lhs; apply congrFun; apply $co (by coerce_discharge) (by coerce_discharge) (by coerce_discharge)
      | goal_is_not_fold $fh; conv => rhs; lhs; apply congrFun; apply $co (by coerce_discharge) (by coerce_discharge)
      | skip))

end Coercions

section ConvertToAccuM

/- Close `a₁ && … && aₖ = (?g && a₁) && … && aₖ` by instantiating the guard slot `?g` to a literal
`true` at the head of a left-associated `&&`-chain (the generalized `fold_accu_Option_*true`
lemmas give every recursive constructor a guard; a guard-free user predicate needs `?g := true`
inserted under `k - 1` trailing conjuncts). -/
macro "true_guard_unify" : tactic =>
  `(tactic|
    first
      | exact (Bool.true_and _).symm
      | exact congrArg (· && _) (Bool.true_and _).symm
      | exact congrArg (· && _) (congrArg (· && _) (Bool.true_and _).symm)
      | exact congrArg (· && _) (congrArg (· && _) (congrArg (· && _) (Bool.true_and _).symm)))

/- Unifier tactic for handling the covert_to_accuM sub-goals.  -/
macro "accu_unify" : tactic =>
  `(tactic|
    (intros; first
      | rfl
      | rflm
      | (simp_bexp; (first | rfl | rflm | true_guard_unify | exact (Bool.and_true _).symm))
      | (simp_all [guard, Option.bind_eq_some_iff, -beq_iff_eq, -Bool.true_and]; (first | rfl | rflm | true_guard_unify | exact (Bool.and_true _).symm))))

macro "accu_convert_one" L:term : tactic =>
  `(tactic|
    first
      | rw [← $L] <;> accu_unify; done
      | rw [← $L] <;> simp_bexp <;> accu_unify; done
      | rw [← $L (by accu_unify) (by accu_unify)] <;> accu_unify; done
      | rw [← $L (by accu_unify) (by accu_unify)]; done)

end ConvertToAccuM

section UnfoldPipeline

open Lean

/- The generic fold → accuM normalization pipeline. -/
syntax "norm_for_unfold" ident term:max ("mergeVia " term:max)?
  "convertVia " "[" term,* "]" ("condVia " term:max)? : tactic

macro_rules
  | `(tactic| norm_for_unfold $fh:ident $co:term $[mergeVia $m:term]?
        convertVia [ $ls:term,* ] $[condVia $cnd:term]?) => do
      let mut alts : Array (TSyntax ``Lean.Parser.Tactic.tacticSeq) := #[]
      for l in ls.getElems do
        alts := alts.push (← `(tacticSeq| accu_convert_one $l))
      if let some c := cnd then
        alts := alts.push (← `(tacticSeq| rw_true_and; rw [← $c]; (try aesop); done))
      let convertStep ← `(tactic| (first $[| $alts]*))
      let core ← `(tactic|
        (first
          | (coerce_fold $fh $co; $convertStep)
          | (simp; coerce_fold $fh $co; $convertStep)))
      match m with
      | some mlem =>
          `(tactic|
            (preprocess
             (repeat' (rw_merge $mlem)) <;> $core))
      | none =>
          `(tactic|
            (preprocess
             $core))

end UnfoldPipeline

macro "norm_for_pure" : tactic =>
  `(tactic| (
    preprocess
    first
      | rfl
      | exact Eq.comm))

macro "norm_for_pick" : tactic =>
  `(tactic| (
    funext
    try simp only [eq_iff_iff, ← Decidable.or_iff_not_imp_left]
    rfl))

macro "norm_for_bind" : tactic =>
  `(tactic| (
    preprocess
    first
      | rfl
      | apply exists_congr; intro; rw [true_and]))

macro "norm_for_bind'" : tactic =>
  `(tactic| (
    preprocess
    rw [exists_comm]
    first
      | rfl
      | apply exists_congr; intro; rw [true_and]))

macro "norm_for_elements" : tactic =>
  `(tactic|
    (preprocess
     accu_simp
     first
       | rfl
       | rw [getElem?_eq_some_iff_indexesOf_getElem?_eq_some]))

macro "normalize_and_apply" : tactic =>
   `(tactic| (
      apply convert ?pf ?arg
      /- simplify the predicate before attempting to normalize it.
         this way we don't repeat simplification for each different normalization strategy -/
      case' pf => unfold_matches; try accu_simp
      first
      | case' arg => apply s_pure _
        case pf => norm_for_pure
      | case' arg => apply s_bind _ _
        first
        | case pf => norm_for_bind' -- TODO Fix this
        | case pf => norm_for_bind
      | case' arg => apply s_pick _ _
        case pf => norm_for_pick
    ))

open Lean Elab Tactic in
/-- The unfold arm of the search, driven by the `unfold_strategy` registry: one alternative per
registered datatype (see `Palamedes.UnfoldStrategy`), each `apply X.s_unfold` followed by the
`norm_for_unfold` pipeline over that type's registered lemmas. `derive_palamedes` registers
every type it derives, so this tactic needs no per-datatype edits. -/
elab "normalize_and_apply_unfold" : tactic => do
  let entries := Palamedes.unfoldStrategies (← getEnv)
  if entries.isEmpty then
    throwError "normalize_and_apply_unfold: no unfold_strategy entries registered"
  -- reference registered constants by `_root_`-rooted idents so open namespaces cannot shadow
  let root (n : Name) : Ident := mkIdent (`_root_ ++ n)
  let mut alts : Array (TSyntax ``Lean.Parser.Tactic.tacticSeq) := #[]
  for e in entries do
    let sUnfold : Lean.Term := root e.sUnfold
    let fold := root e.fold
    let coerce : Lean.Term := root e.coerce
    let merge : Lean.Term := root e.merge
    let convs : Syntax.TSepArray `term "," := .ofElems (e.convert.map fun n => (root n : Lean.Term))
    let norm ← match e.cond with
      | some c =>
        `(tactic| norm_for_unfold $fold $coerce mergeVia $merge
            convertVia [$convs,*] condVia $(root c))
      | none =>
        `(tactic| norm_for_unfold $fold $coerce mergeVia $merge
            convertVia [$convs,*])
    alts := alts.push (← `(tacticSeq|
      case' arg => apply $sUnfold:term _
      case pf => $norm:tactic))
  evalTactic (← `(tactic| (
    goal_is_eq_or_and
    apply convert ?pf ?arg
    case' pf => try accu_simp
    first $[| $alts]*)))

end Normalizers

section CaseSplit

open Lean Lean.Meta Lean.Elab.Tactic Aesop Palamedes.Gen.CorrectGen

/- The datatypes the case-split rule can scrutinise, each paired with its `s_case*` lemma, come
   from the `case_split` registry (see `Palamedes.CaseSplit`): every `@[case_split]` lemma has
   the shape `(scrut) (h : ∀ {a}, P a scrut = Q a) (cases…)`, so one routine drives them all
   regardless of how many constructors the datatype has. -/

private def isCorrectGenOr (tgt : Expr) : MetaM Bool := do
  match (← instantiateMVars tgt).getAppFnArgs with
  | (``CorrectGen, #[_, p]) => lambdaTelescope p fun _ body => pure (body.isAppOf ``Or)
  | _ => pure false

/-- Apply `lemmaName` with `scrut` as the scrutinee: assign the scrutinee subgoal, discharge the
    `∀ {a}, P a scrut = Q a` premise with `intros; rflm` (which synthesises `P` by generalising
    `scrut` out of the goal predicate), and return the remaining case subgoals. Throws if `scrut`
    is not usable here (e.g. `rflm` can't close the premise). -/
private def caseSplitWith (goal : MVarId) (scrut : Expr) (lemmaName : Name) :
    MetaM (List MVarId) := do
  let newGoals ← goal.apply (← mkConstWithFreshMVarLevels lemmaName)
  let scrutTy ← inferType scrut
  let some scrutGoal ← newGoals.findM? (fun g => do isDefEq (← g.getType) scrutTy)
    | throwError "caseSplitWith: no scrutinee subgoal"
  scrutGoal.assign scrut
  let mut caseGoals := #[]
  for g in newGoals.filter (· != scrutGoal) do
    let ty ← g.getType
    if ← forallTelescopeReducing ty (fun _ b => pure (b.isAppOf ``Eq)) then
      -- the `h : ∀ {a}, P a scrut = Q a` premise; `rflm` also assigns the predicate mvar `P`
      let remaining ← Lean.Elab.Tactic.run g (evalTactic (← `(tactic| (intros; rflm)))) |>.run'
      unless remaining.isEmpty do throwError "caseSplitWith: rflm left goals open"
    else if ← forallTelescopeReducing ty (fun _ b => pure (b.isAppOf ``CorrectGen)) then
      caseGoals := caseGoals.push g
    -- else: an inferred metavariable (e.g. the predicate `P`), discharged by `rflm` above; skip it.
  return caseGoals.toList

/-- For `CorrectGen (fun a => _ ∨ _)` goal it offers one rule application per candidate scrutinee — each
    local hypothesis that occurs in the predicate and whose type is a supported datatype — and lets
    Aesop's own search pick the one whose case subgoals close. This subsumes the old
    `clear_unused_assumptions; nth_assumption k` brute-force enumeration. -/
@[aesop unsafe 5% (rule_sets := [synthesis]) tactic]
def caseSplitRuleTac : RuleTac := fun input => do
  input.goal.withContext do
    let tgt ← input.goal.getType
    unless ← isCorrectGenOr tgt do
      throwError "caseSplitRuleTac: goal is not a CorrectGen of a disjunction"
    let caseSplitLemmas := Palamedes.caseSplitLemmas (← getEnv)
    let initialState ← saveState
    let mut apps := #[]
    for decl? in (← getLCtx).decls.toList do
      let some decl := decl? | continue
      if decl.isImplementationDetail then continue
      unless tgt.containsFVar decl.fvarId do continue
      let declTy ← instantiateMVars (← inferType decl.toExpr)
      let some lemmaName := (caseSplitLemmas.find? (declTy.isConstOf ·.1)).map (·.2) | continue
      try
        let caseGoals ← caseSplitWith input.goal decl.toExpr lemmaName
        let subgoals ← caseGoals.toArray.mapM (mvarIdToSubgoal input.goal ·)
        let postState ← saveState
        apps := apps.push
          { postState, goals := subgoals, scriptSteps? := none, successProbability? := none }
      catch _ => pure ()
      initialState.restore
    if apps.isEmpty then
      throwError "caseSplitRuleTac: no applicable scrutinee"
    return ⟨apps⟩

end CaseSplit

section AesopRules

/-

For performance, we want to abide by two heuristics:
1) `simp` as infrequently as possible, and
2) prune the search tree as often as possible.

We accomplish goal 1 by factoring out the `simp` steps in the normalization
tactics above, and we accomplish goal 2 here by trying every `arb` lemma
that can close a goal before trying any lemmas that generate new subgoals.

-/
-- The `s_arb*` closers that used to be enumerated here are now `@[aesop safe apply]` tags on
-- the definitions themselves (see the `Data/` modules).
add_aesop_rules safe (rule_sets := [synthesis]) [
  (by (repeat apply duncurry); intro),
]

add_aesop_rules 99% (rule_sets := [synthesis]) [
  (by assumption),
  (by normalize_and_apply),
  (by normalize_and_apply_unfold),
  (by apply s_arbAtom _),
  (by apply s_gt),
  (by apply s_mod2_partial),
  (by apply s_lt_partial),
  (by apply s_between_partial),
  (by apply (s_between (by first | aesop | omega))),
  (by goal_is_eq; apply convert (by norm_for_elements) (s_elements_partial _)),
]

-- The per-datatype/per-scrutinee `s_case*` enumeration that used to live here is now the single
-- `caseSplitRuleTac` rule (see section `CaseSplit`), registered via `@[aesop]`.

end AesopRules

section API

macro "cgenerator_search" : tactic =>
  `(tactic|
    aesop
      (rule_sets := [-default, -builtin, synthesis])
      (config := {enableSimp := false, maxRuleApplications := 1000}))

macro "cgenerator_search?" : tactic =>
  `(tactic|
    aesop?
      (rule_sets := [-default, -builtin, synthesis])
      (config := {enableSimp := false, maxRuleApplications := 1000}))

end API
