import Palamedes.Gen
import Palamedes.Support
import Palamedes.OptimizeCongr
import Palamedes.UnfoldStrategy

open Lean Elab Command Term Meta

namespace Palamedes

open _root_.Palamedes.Gen

/-!
# Correct-by-Construction Optimizer

`optimizeGen` optimizes a generator, ideally with the goal of bubbling any `assume` statements up to
the nearest choice point and removing unnecessary backtracking. The optimizer is
correct-by-construction and builds a proof of correctness as it goes.
-/

/-- A rewrite result: the rewritten expression `expr` and the twin `support_*` lemma that justifies
it. The lemma's orientation (whether it is stated `support <original> = support expr` or the other
way round) is recovered when the proof is built, in `mkLeafProof`. -/
abbrev GenRewriteResult := Expr × Name

mutual

/-- Can some `assume` inside `e` bubble up to the *head* of `e`?

We descend the spine, accumulating in `crossed` the value-binders introduced on the way (those a
`bind` continuation binds). On reaching `assume b _`, the guard `b` reaches the head iff it mentions
none of them. Each case mirrors the lift lemma that would fire:

* `bind x f` — descend the scrutinee `x` (`support_assume_bind` lifts unconditionally) and the
  continuation under its binder `a` (`support_bind_assume` lifts iff the guard avoids `a`). When `x`
  is `pure a₀` we descend `f a₀` instead: `support_pure_bind` fires first, so a guard that mentioned
  the bound value becomes concrete and may now lift.
* `pick x y` — descend both arms. An assume in a single arm clears the pick
  by degrading to a `dite` (`support_assume_pick`); when both arms share the guard it lifts cleanly
  (`support_pick_assume_same`). Either outcome is wanted, so single-arm hits count.
* `dite`/`ite` — descend the branches (their proof binders never enter `crossed`).
* `indexed` — opaque barrier: a guard inside the fueled fixpoint is re-asserted per unfolding and
  cannot be hoisted.
* `ret`, or any non-`Gen` head — nothing to lift. -/
partial def assumeReachesHead (e : Expr) (crossed : Array FVarId) : MetaM Bool := do
  match_expr ← withReducible (reduce e) with
  | assume _ b g =>
    if crossed.all (fun fv => !b.containsFVar fv) then return true
    else assumeUnderBinder g crossed        -- a deeper assume commutes up past this stuck one
  | bind _ _ _ _ x f =>
    match_expr x with
    | pure _ _ _ a => assumeReachesHead (f.beta #[a]) crossed
    | _ => return (← assumeReachesHead x crossed) || (← assumeUnderBinder f crossed)
  | pick _ x y => return (← assumeReachesHead x crossed) || (← assumeReachesHead y crossed)
  | dite _ _ _ t f => return (← assumeUnderBinder t crossed) || (← assumeUnderBinder f crossed)
  | ite _ _ _ t f => return (← assumeReachesHead t crossed) || (← assumeReachesHead f crossed)
  -- A per-datatype `unfold` combinator (a `partial_fixpoint`) is an opaque barrier: a guard inside
  -- the fixpoint is re-asserted per unfolding and cannot be hoisted. It falls through to `_`.
  | _ => return false

/-- Descend under one leading binder. A value binder enters `crossed` (a guard may depend on it); a
proof binder (from `assume`/`dite`) does not — guards are `Bool`, so by proof irrelevance they
cannot mention it. -/
partial def assumeUnderBinder (f : Expr) (crossed : Array FVarId) : MetaM Bool := do
  forallBoundedTelescope (← inferType f) (some 1) fun xs _ => do
    let #[x] := xs | return false
    let crossed := if ← Meta.isProof x then crossed else crossed.push x.fvarId!
    assumeReachesHead (f.beta #[x]) crossed

end

/-- Single head rewrite of a `bind` node `x >>= f`. Mirrors the monad-law / commuting rules, and
additionally reports the twin `support_*` lemma proving the rewrite is support-preserving. -/
def optimizeBind? (x f : Expr) : MetaM (Option GenRewriteResult) :=
  match_expr x with
  -- pure_bind : pure a >>= f ~~> f a
  | pure _ _ _ a => return some (Expr.app f a, ``support_pure_bind)
  -- bind_bind : (x >>= f) >>= g ~~> x >>= (fun x -> f x >>= g)
  | bind _ _ _ _ x' g => do
    let .forallE _ argTy _ _ ← inferType g | return none
    let f' ← withLocalDecl `a .default argTy fun a => do
      mkLambdaFVars #[a] (← mkAppM ``bind #[.app g a, f])
    return some (← mkAppM ``bind #[x', f'], ``support_bind_bind)
  -- assume_bind : assume b g >>= f ~~> assume b (fun h => g h >>= f)
  | assume _ b g => do
    let f' ← withLocalDecl `h .default (← mkEq b (.const ``true [])) fun h => do
      mkLambdaFVars #[h] (← mkAppM ``bind #[.app g h, f])
    return some (← mkAppM ``assume #[b, f'], ``support_assume_bind)

  -- These three rules push a bind down through a branch (`pick`/`dite`/`ite`), duplicating the
  -- continuation `f`. That only pays off when it lets an `assume` bubble up past the branch, so each
  -- is gated on `assumeReachesHead`: distribute iff a resulting arm exposes a liftable assume.
  -- Branches with nothing to harvest are left alone — which is what bounds the term-size blowup that
  -- distributing nested `pick`s would otherwise cause.
  | pick _ x y => do
    let xb ← mkAppM ``bind #[x, f]
    let yb ← mkAppM ``bind #[y, f]
    unless (← assumeReachesHead xb #[]) || (← assumeReachesHead yb #[]) do return none
    return some (← mkAppM ``pick #[xb, yb], ``support_pick_bind)
  | dite _ P _ trueCase falseCase => do
    let trueCase' ← withLocalDecl `h .default P fun h => do
      mkLambdaFVars #[h] (← mkAppM ``bind #[.app trueCase h, f])
    let falseCase' ← withLocalDecl `h .default (.app (.const ``Not []) P) fun h => do
      mkLambdaFVars #[h] (← mkAppM ``bind #[.app falseCase h, f])
    unless (← assumeUnderBinder trueCase' #[]) || (← assumeUnderBinder falseCase' #[]) do return none
    return some (← mkAppM ``dite #[P, trueCase', falseCase'], ``support_if_bind)
  | ite _ P _ trueCase falseCase => do
    let trueCase' ← mkAppM ``bind #[trueCase, f]
    let falseCase' ← mkAppM ``bind #[falseCase, f]
    unless (← assumeReachesHead trueCase' #[]) || (← assumeReachesHead falseCase' #[]) do return none
    return some (← mkAppM ``ite #[P, trueCase', falseCase'], ``support_ite_bind)

  | _ => do
    lambdaBoundedTelescope f 1 fun args body => do
      -- bind_assume : x >>= fun a => assume b g ~~> assume b (fun h => (x >>= fun a => g h))
      --               (where a is not free in b)
      let #[a] := args | return none
      let_expr assume _ b g := body | return none

      -- We may only float `assume b …` above the binder for `a` if `b` doesn't mention `a` (a
      -- scoping requirement). This is conservative: a `b` that's a metavariable possibly depending
      -- on `a` slips past `containsFVar`, so we skip the rewrite rather than risk a malformed term.
      if b.containsFVar a.fvarId! then return none

      let f' ← withLocalDecl `h .default (← mkEq b (.const ``true [])) fun h => do
        mkLambdaFVars #[h] (← mkAppM ``bind #[x, ← mkLambdaFVars #[a] (.app g h)])
      return some (← mkAppM ``assume #[b, f'], ``support_bind_assume)

/-- Single head rewrite of an `assume` node `assume b f`. When the guard `b` is decidably *true*, the
guard never filters: `assume b f ~~> f h` (twin lemma `support_assume_true`), which deletes the dead
`empty` else-branch. This is the step that makes a satisfiable-but-syntactically-present `assume`
disappear, so that a total generator ends up genuinely `Fail`-free after optimization. A guard that is
not closed (mentions bound values) or not provably true is left alone — that is a genuine filter. -/
def optimizeAssume? (b f : Expr) : MetaM (Option GenRewriteResult) := do
  -- Only discharge a guard we can *close*: no metavariables, and definitionally `true`. A guard that
  -- mentions bound generator values (e.g. an unfold's seed) is not closed and stays as a real filter.
  if b.hasExprMVar then return none
  unless ← isDefEq b (.const ``true []) do return none
  let h ← mkDecideProof (← mkEq b (.const ``true []))
  return some (f.beta #[h], ``support_assume_true)

/-- Single head rewrite of a `pick` node `pick x y`. Reports the twin `support_*` lemma alongside
the rewritten expression. -/
def optimizePick? (x y : Expr) : MetaM (Option GenRewriteResult) :=
  match_expr x with
  | assume _ b f =>
    match_expr y with
    | assume _ b' g =>
      -- if both x and y are `assume`s, then we have one of two cases:
      -- if they assume the same boolean:
        -- assume_pick : pick (assume b f) (assume b g) ~~> assume b (pick f g)
      if b == b' then do
        let c ← mkEq b (.const ``true [])
        let f' ← withLocalDecl `h .default c fun h => do
          mkLambdaFVars #[h] (← mkAppM ``pick #[.app f h, .app g h])
        return some (← mkAppM ``assume #[b, f'], ``support_pick_assume_same)
      -- otherwise they assume different booleans:
        -- assume_pick : pick (assume b f) y ~~> if h : b then pick (f h) y else y
      else do
        let c ← mkEq b (.const ``true [])
        let fPos ← withLocalDecl `h .default c fun h => do
          mkLambdaFVars #[h] (← mkAppM ``pick #[.app f h, y])
        let fNeg ← withLocalDecl `h .default (.app (.const ``Not []) c) fun h =>
          mkLambdaFVars #[h] y
        return some (← mkAppM ``dite #[c, fPos, fNeg], ``support_assume_pick)
    -- if only x is an `assume`:
      -- assume_pick : pick (assume b f) y ~~> if h : b then pick (f h) y else y
    | _ => do
      let c ← mkEq b (.const ``true [])
      let fPos ← withLocalDecl `h .default c fun h => do
        mkLambdaFVars #[h] (← mkAppM ``pick #[.app f h, y])
      let fNeg ← withLocalDecl `h .default (.app (.const ``Not []) c) fun h =>
        mkLambdaFVars #[h] y
      return some (← mkAppM ``dite #[c, fPos, fNeg], ``support_assume_pick)
  | _ =>
    match_expr y with
    -- if only y is an `assume`:
      -- pick_assume : pick x (assume b f) ~~> if h : b then pick x (f h) else x
    | assume _ b f => do
      let c ← mkEq b (.const ``true [])
      let fPos ← withLocalDecl `h .default c fun h => do
        mkLambdaFVars #[h] (← mkAppM ``pick #[x, .app f h])
      let fNeg ← withLocalDecl `h .default (.app (.const ``Not []) c) fun h =>
        mkLambdaFVars #[h] x
      return some (← mkAppM ``dite #[c, fPos, fNeg], ``support_pick_assume)
    | _ => return none

/-! ## Pick-chain flattening -/

/-- Elements of a literal `List` expression (`a :: b :: … :: []`), or `none` if any spine node is
not a `cons`/`nil` constructor application. -/
private partial def listLitElems? (e : Expr) : Option (List Expr) :=
  match e.getAppFnArgs with
  | (``List.cons, #[_, h, t]) => (h :: ·) <$> listLitElems? t
  | (``List.nil, #[_]) => some []
  | _ => none

/-- Match `oneOf (x :: xs) h` with a literal branch list — the shape the flatten pass itself emits —
returning the head `x`, the tail expression `xs`, its elements, and the nonemptiness proof `h`. -/
private def oneOfLit? (e : Expr) : Option (Expr × Expr × List Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Gen.oneOf, #[_, gs, h]) =>
    match gs.getAppFnArgs with
    | (``List.cons, #[_, x, xs]) => do
      let elems ← listLitElems? xs
      return (x, xs, elems, h)
    | _ => none
  | _ => none

/-- Flatten-pass head rewrite of `pick x y`: collect both arms' branches — an arm contributes its
elements when it is itself a literal `oneOf` (an already-flattened subtree), and itself otherwise —
and emit one uniform `oneOf` over all of them. Because children are flattened before their parent,
this collapses an arbitrarily nested `pick` tree (either spine direction) into a single n-ary
uniform choice.

Returns the rewritten expression together with its support-preservation proof: the twin lemmas'
statements mention `++`, which `mkLeafProof`'s unifier cannot invert against the flat literal list
we emit, so the proof is instantiated explicitly here instead of found by unification. The two
sides remain definitionally equal (`++` on literals reduces), which is all downstream proof
composition needs. -/
private def flattenPick? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match_expr e with
  | Gen.pick _ x y => do
    let (elems, proof) ←
      match oneOfLit? x, oneOfLit? y with
      | none, none => do
        pure ([x, y], ← mkAppM ``support_pick_flatten #[x, y])
      | some (xh, xt, xelems, hx), none => do
        pure (xh :: xelems ++ [y], ← mkAppM ``support_pick_flatten_left #[xh, xt, hx, y])
      | none, some (yh, yt, yelems, hy) => do
        pure (x :: yh :: yelems, ← mkAppM ``support_pick_flatten_right #[x, yh, yt, hy])
      | some (xh, xt, xelems, hx), some (yh, yt, yelems, hy) => do
        pure (xh :: xelems ++ yh :: yelems,
          ← mkAppM ``support_pick_flatten_both #[xh, xt, hx, yh, yt, hy])
    let tl ← mkListLit (← inferType x) elems.tail
    let gs ← mkAppM ``List.cons #[elems.head!, tl]
    let hne ← mkAppM ``List.cons_ne_nil #[elems.head!, tl]
    let e' ← mkAppM ``Gen.oneOf #[gs, hne]
    return some (e', proof)
  | _ => return none

/-! ## Depth-indexed weighting: `SchedulePolicy` and `installTuning`

A schedule is affine in the recursion depth, `wⱼ(d) = aⱼ + bⱼ · d`, so mean offspring can start above
1 near the root and fall below 1 with depth. Decay is base-weight *growth*, never recursive-weight
shrinkage: a weight of `0` would drop its branch from the support, so every weight stays `≥ 1` and a
deep recursion becomes rarer, never impossible. -/

/-- An affine weight schedule `d ↦ base + growth · d`. Invariant: `base ≥ 1`. The `(base, growth)`
pair is exactly one entry of a Basalt `Tuning`; a `SchedulePolicy` produces these per branch and
`SchedulePolicy.materialize` lays them out into a `Tuning`. -/
structure Schedule where
  base : Nat
  growth : Nat
  deriving Repr, Inhabited

/-- A `frequency` site collected by `installTuning`; the internal form of Basalt's `Site`. `offset` is
the site's first index into the flat `Tuning.schedules` array. -/
structure TuningSiteInfo where
  name : Name
  offset : Nat
  arity : Nat
  holes : Array Nat
  deriving Inhabited

/-- Threaded state for the `installTuning` pass: the next free offset into `Tuning.schedules` and the
sites collected so far, in assignment order. -/
structure TuningState where
  nextOffset : Nat := 0
  sites : Array TuningSiteInfo := #[]
  deriving Inhabited

/-- How to weight a branch, as a function of how many recursive children it has.

A policy is untrusted: it can only tune the distribution, never the support, since the
support-preservation proof is composed regardless of what it proposes. -/
structure SchedulePolicy where
  weight : Nat → Schedule

/-- A general, datatype-agnostic decay family, keyed only on whether a branch *closes* the recursion.

Continuing branches (≥1 recursive child) are held at the constant `root`; closing branches (0
children) grow as `1 + rate·d`. So at the root the recursion is favored `root : 1` — mean offspring
starts supercritical when `root > 1` — and as depth grows the closing branches dominate and mean
offspring falls to 0, forcing termination. Two knobs, both interpretable:

* `root` — how bushy the top of the value is (the root branching bias);
* `rate` — how fast the recursion is driven closed with depth.

Unlike `SchedulePolicy.stlc` this makes no per-arity distinction, so it carries no tuning specific to
any one datatype. The named points below (`gentle`/`moderate`/`steep`) are the ready-made choices. -/
def SchedulePolicy.decayBy (root rate : Nat) : SchedulePolicy where
  weight
    | 0 => { base := 1, growth := rate }
    | _ => { base := root, growth := 0 }

/-- Slow decay: the recursion stays live several levels down, giving deeper and larger values. -/
def SchedulePolicy.gentle : SchedulePolicy := .decayBy 3 4

/-- A general-purpose middle decay rate: supercritical at the root, closed within a few levels. -/
def SchedulePolicy.moderate : SchedulePolicy := .decayBy 3 12

/-- Fast decay: the recursion closes almost immediately, giving shallow values that terminate hard. -/
def SchedulePolicy.steep : SchedulePolicy := .decayBy 3 30

/-- The STLC-tuned policy: a branch that closes the recursion grows fastest with depth, one with a
single child grows more slowly, and a branch with two or more is held constant — decayed *relative
to* the others, never toward zero.

The coefficients are hand-tuned on `genWellTyped`, and its distribution is pinned in
`ScheduleMeasurements.lean`; this is *not* a good general default (it encodes an arity preference
specific to STLC's term type). Materialize it against a generator's sites with
`SchedulePolicy.stlc.materialize gen.sites` and pass the result to `gen.tuned` (see `derive_tuning`).
Eventually a drift solve should compute coefficients like these per site. -/
def SchedulePolicy.stlc : SchedulePolicy where
  weight
    | 0 => { base := 1, growth := 30 }
    | 1 => { base := 1, growth := 14 }
    | _ => { base := 4, growth := 0 }

/-- Lay a `SchedulePolicy` over a site table into a `Tuning`: each branch's `(base, growth)` is
`policy.weight` of its recursive-child count (`Site.holes`), placed at flat index `offset + j`. Turns
a coarse arity-keyed policy into the per-site `Tuning` a `.tuned` generator reads. -/
def SchedulePolicy.materialize (policy : SchedulePolicy) (sites : Array Site) : Tuning := Id.run do
  let total := sites.foldl (init := 0) fun acc s => max acc (s.offset + s.arity)
  let mut arr : Array (Nat × Nat) := Array.replicate total (1, 0)
  for s in sites do
    for j in [0:s.arity] do
      let sched := policy.weight (s.holes.getD j 0)
      arr := arr.set! (s.offset + j) (sched.base, sched.growth)
  return ⟨arr⟩

/-- Recursive-field counts for each constructor of a base functor `XF`: a field is a hole when its
type is the carrier (the last parameter of `XF`). -/
def baseCtorHoles (fName : Name) : MetaM (Std.HashMap Name Nat) := do
  let iv ← getConstInfoInduct fName
  let mut m : Std.HashMap Name Nat := {}
  for cn in iv.ctors do
    let ci ← getConstInfoCtor cn
    let n ← forallBoundedTelescope ci.type iv.numParams fun params body => do
      let some carrier := params.back? | return 0
      forallTelescope body fun fields _ =>
        fields.foldlM (init := 0) fun acc f => do
          return if (← inferType f) == carrier then acc + 1 else acc
    m := m.insert cn n
  return m

/-- How many recursive children one branch of a step generator produces: walk it to the
`pure (XF.c …)` it ends in and read the count off `c`.

A branch ending in several constructors (it contains a nested choice or a `dite`) is scored by its
largest count. Over-counting is the safe direction — it biases the branch toward a constant weight,
which can only make the generator terminate more readily. -/
partial def branchHoles (holes : Std.HashMap Name Nat) (e : Expr) : MetaM Nat := do
  let underBinder (f : Expr) : MetaM Nat := do
    forallBoundedTelescope (← inferType f) (some 1) fun xs _ => do
      let #[x] := xs | return 0
      branchHoles holes (f.beta #[x])
  match_expr ← withReducible (reduce e) with
  | pure _ _ _ a =>
    let some c := a.getAppFn.constName? | return 0
    return holes.getD c 0
  | bind _ _ _ _ _ f => underBinder f
  | assume _ _ f => underBinder f
  | dite _ _ _ t f => return max (← underBinder t) (← underBinder f)
  | ite _ _ _ t f => return max (← branchHoles holes t) (← branchHoles holes f)
  | Gen.pick _ x y => return max (← branchHoles holes x) (← branchHoles holes y)
  | Gen.oneOf _ gs _ =>
    let some elems := listLitElems? gs | return 0
    elems.foldlM (init := 0) fun acc g => return max acc (← branchHoles holes g)
  -- Children are descended into before the head rewrite, so an inner choice is already a `frequency`
  -- by the time the outer one is scored. Omitting this case scores it 0 holes — the unsafe direction,
  -- since a decay policy grows a 0-hole branch's weight fastest, which on a recursive branch is wrong.
  | Gen.frequency _ gs _ =>
    let some elems := listLitElems? gs | return 0
    elems.foldlM (init := 0) fun acc p => do
      match p.getAppFnArgs with
      | (``Prod.mk, #[_, _, _, g]) => return max acc (← branchHoles holes g)
      | _ => return acc
  | _ => return 0

/-! ### `installTuning` — `θ`-threaded reweighting

Rewrites each uniform `oneOf` to a `frequency` whose weights read a runtime `θ : Tuning`
(`Tuning.weight θ (offset+j) d`), recording each site's block layout as a `TuningSiteInfo`. Positivity
is `Tuning.weight_pos`, which holds for every `θ`, so the pass is total in `θ`. -/

private def mkTunedWeight (θ : Expr) (idx : Nat) (depth : Expr) : MetaM Expr :=
  mkAppM ``Tuning.weight #[θ, mkNatLit idx, depth]

private def mkTunedWeightPos (θ : Expr) (idx : Nat) (depth : Expr) : MetaM Expr :=
  mkAppM ``Tuning.weight_pos #[θ, mkNatLit idx, depth]

/-- `∀ p ∈ gs', 0 < p.1` for a `θ`-weighted branch list, folded link-by-link from `Tuning.weight_pos`
at each branch's flat index. -/
private def mkAllPosTuning (α θ : Expr) (pairs : List (Expr × Expr)) (idxs : List Nat)
    (depth : Expr) : MetaM Expr := do
  match pairs, idxs with
  | [], _ => mkAppM ``allPos_nil #[α]
  | (w, g) :: ps, i :: is =>
    let tl ← mkListLit (← mkAppM ``Prod #[mkConst ``Nat, ← mkAppM ``Gen #[α]])
      (← ps.mapM fun (w, g) => mkAppM ``Prod.mk #[w, g])
    let hw ← mkTunedWeightPos θ i depth
    mkAppM ``allPos_cons #[α, w, g, tl, hw, ← mkAllPosTuning α θ ps is depth]
  | _, _ => throwError "installTuning: branch/index length mismatch"

/-- The head rewrite: a uniform `oneOf` becomes a `frequency` weighted by `Tuning.weight θ (offset+j)
d`, with its support-preservation proof, appending a `TuningSiteInfo`. Fires on every literal `oneOf`
(one outside a recursion reads its weights at depth `0`). Children rewrite before their parent, so
offsets run innermost-first — consistent because the one pass both assigns and records them. -/
private def installTuning? (θ : Expr) (st : IO.Ref TuningState) (declName : Name)
    (depth? : Option (Expr × Name)) (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match_expr e with
  | Gen.oneOf α gs h => do
    let some elems := listLitElems? gs | return none
    if elems.isEmpty then return none
    -- depth expr (or `0` outside a recursion) and per-branch recursive-child counts
    let (depth, holes) ← match depth? with
      | some (d, typeName) => do
          let hm ← baseCtorHoles (typeName.appendAfter "F")
          let hs ← elems.mapM (branchHoles hm)
          pure (d, hs.toArray)
      | none => pure (mkNatLit 0, Array.replicate elems.length 0)
    let cur ← st.get
    let offset := cur.nextOffset
    let arity := elems.length
    let siteName := declName ++ Name.mkSimple s!"site{cur.sites.size}"
    let idxs := (List.range arity).map (offset + ·)
    let ws ← idxs.mapM (mkTunedWeight θ · depth)
    let pairs := ws.zip elems
    let pairExprs ← pairs.mapM fun (w, g) => mkAppM ``Prod.mk #[w, g]
    let prodTy ← mkAppM ``Prod #[mkConst ``Nat, ← mkAppM ``Gen #[α]]
    let gs' ← mkListLit prodTy pairExprs
    -- the `frequency` side-goal `0 < Σ wⱼ(d)`, from the first weight's positivity alone
    let hw0 ← mkTunedWeightPos θ offset depth
    let tl ← mkListLit prodTy pairExprs.tail!
    let h' ← mkAppM ``sum_fst_pos_cons #[α, ws.head!, elems.head!, tl, hw0]
    let e' ← mkAppM ``Gen.frequency #[gs', h']
    let hpos ← mkAllPosTuning α θ pairs idxs depth
    let hsnd ← mkEqRefl gs
    let proof ← mkAppM ``support_oneOf_reweight #[α, gs, gs', hsnd, hpos, h, h']
    st.set { nextOffset := offset + arity, sites := cur.sites.push ⟨siteName, offset, arity, holes⟩ }
    return some (e', proof)
  | _ => return none

/-- The head-rewrite sets a traversal can apply. `.main` is the assume-floating / monad-law set;
`.flatten` collapses `pick` trees into `oneOf` and must run as a separate later pass, because
`.main`'s bind-distribution rules create and extend `pick` chains (and need the picks intact to
float assumes out of them). `.installTuning` is not run here — `derive_tuning` applies it after
elaboration, on the finished term.

`.flatten`'s `distribute` flag additionally pushes a choice into a `dite`/`ite` arm
(`distributeChoiceDite?`) so a choice nested under a case split becomes a flat `oneOf` per branch —
one `derive_tuning` site per constructor rather than one shared across the case split. `optimizeGen`
passes `distribute := true`, so every synthesized generator ships with that per-constructor shape. -/
inductive OptPass | main | flatten (distribute : Bool)
  | installTuning (θ : Expr) (st : IO.Ref TuningState) (declName : Name)

/-! ## Proof-carrying traversal -/

/-- `support e`. -/
private def mkSupport (e : Expr) : MetaM Expr := mkAppM ``Gen.support #[e]

/-- `rfl : support e = support e`. -/
private def mkSupportRefl (e : Expr) : MetaM Expr := do mkEqRefl (← mkSupport e)

/-- `fun xs => rfl : ∀ xs, support (f xs) = support (f xs)`, for an unchanged (possibly
multi-argument) binder `f` whose codomain is a `Gen`. -/
private def mkBinderRefl (f : Expr) : MetaM Expr := do
  forallTelescope (← inferType f) fun xs _ => do
    mkLambdaFVars xs (← mkSupportRefl (f.beta xs))

/-- Prove `support lhs = support rhs` using the twin lemma `lemmaName`, in whichever orientation it
is stated. -/
private def mkLeafProof (lemmaName : Name) (lhs rhs : Expr) : MetaM Expr := do
  let lhsS ← mkSupport lhs
  let rhsS ← mkSupport rhs
  -- Fresh lemma instance per attempt, so a failed `isDefEq` can't pollute the next one (the goal
  -- itself is metavariable-free).
  let tryOrient (a b : Expr) : MetaM (Option Expr) := do
    let lem ← mkConstWithFreshMVarLevels lemmaName
    let (mvars, _, concl) ← forallMetaTelescope (← inferType lem)
    if ← isDefEq concl (← mkEq a b) then return some (← instantiateMVars (mkAppN lem mvars))
    else return none
  if let some pf ← tryOrient lhsS rhsS then return pf
  if let some pf ← tryOrient rhsS lhsS then return (← mkEqSymm pf)
  throwError "optimizer: twin lemma `{lemmaName}` matches neither orientation of goal\
    {indentExpr (← mkEq lhsS rhsS)}"

/-- Match `@dite α P inst t f`, returning `(P, inst, t, f)`. -/
private def matchDite? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  match_expr e with
  | dite _ P inst t f => some (P, inst, t, f)
  | _ => none

/-- Flatten-pass distribution of a choice into a `dite` arm (`optimizeGen` enables it via
`distribute := true`). The synthesizer emits a state class's choice as `pick x (dite c t f)` when one
constructor (`x`) is unconditional and others are gated on a context condition `c`. Left as is,
`flattenPick?` collapses it to `oneOf [x, dite c (oneOf ..) ..]` — a choice *nested* under the `dite`,
so the inner `oneOf` becomes a single `installTuning` site shared across branches rather than one site
per constructor. Distributing gives `dite c (pick x t) (pick x f)`; re-flattening each arm then yields
a flat `oneOf` per branch, addressable per constructor.

**Duplication is bounded on purpose.** Distribution copies the *non-conditional* arm (`x`/`y`) into
both branches, so it fires only when that arm is a leaf — a branch whose base-functor constructor has
no recursive child (0 holes). A recursive arm is left nested rather than duplicated: the site stays
less-well-tuned, never blown up, and support is preserved either way. Requires a depth in scope, so
`holes` is meaningful and reweighting has somewhere to land; outside a recursion it declines. -/
private def distributeChoiceDite? (depth : Option (Expr × Name)) (e : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let some (_, typeName) := depth | return none
  let_expr Gen.pick _ x y := e | return none
  let holes ← baseCtorHoles (typeName.appendAfter "F")
  -- `dite P inst (fun h => mkT h) (fun h => mkF h)`, preserving the original decidability instance.
  let mkDite (P inst : Expr) (mkT mkF : Expr → MetaM Expr) : MetaM Expr := do
    let t' ← withLocalDecl `h .default P fun h => do mkLambdaFVars #[h] (← mkT h)
    let f' ← withLocalDecl `h .default (.app (.const ``Not []) P) fun h => do
      mkLambdaFVars #[h] (← mkF h)
    mkAppOptM ``dite #[none, P, inst, t', f']
  match matchDite? y with
  -- `pick x (dite c t f)` with `x` a leaf → `dite c (pick x (t h)) (pick x (f h))`.
  | some (P, inst, t, f) =>
    if (← branchHoles holes x) != 0 then return none
    let e' ← mkDite P inst (fun h => mkAppM ``pick #[x, .app t h])
                           (fun h => mkAppM ``pick #[x, .app f h])
    return some (e', ← mkLeafProof ``support_pick_dite_right e e')
  | none =>
  match matchDite? x with
  -- `pick (dite c t f) y` with `y` a leaf → `dite c (pick (t h) y) (pick (f h) y)`.
  | some (P, inst, t, f) =>
    if (← branchHoles holes y) != 0 then return none
    let e' ← mkDite P inst (fun h => mkAppM ``pick #[.app t h, y])
                           (fun h => mkAppM ``pick #[.app f h, y])
    return some (e', ← mkLeafProof ``support_pick_dite_left e e')
  | none => return none

/-- Lift the child proofs `hyps` through a constructor with congruence lemma `lemmaName`, proving
`support node = support node'`. The lemma's structural arguments are solved by unifying its
conclusion with the (concrete) goal; whatever binders that leaves unassigned are exactly the
congruence hypotheses, which we discharge with `hyps`. Each hypothesis is matched to a child proof
*by type* rather than by position, so the lemma's hypothesis order need not track its argument
order. This tolerates implicit and interleaved hypotheses (e.g. `support_caseTy_congr`). -/
private def mkCongrProof (lemmaName : Name) (node node' : Expr) (hyps : Array Expr) : MetaM Expr := do
  let goal ← mkEq (← mkSupport node) (← mkSupport node')
  let lem ← mkConstWithFreshMVarLevels lemmaName
  let (mvars, _, concl) ← forallMetaTelescope (← inferType lem)
  unless ← isDefEq concl goal do
    throwError "optimizer: congruence lemma `{lemmaName}` does not match goal{indentExpr goal}"
  let mut hypMvars := #[]
  for m in mvars do
    unless ← m.mvarId!.isAssigned do
      hypMvars := hypMvars.push m
  unless hypMvars.size == hyps.size do
    throwError "optimizer: `{lemmaName}` expects {hypMvars.size} hypotheses, given {hyps.size}"
  let mut pool := hyps.toList
  for m in hypMvars do
    let mut rest : List Expr := []
    let mut matched := false
    for h in pool do
      if !matched && (← isDefEq m h) then
        matched := true
      else
        rest := rest ++ [h]
    unless matched do
      throwError "optimizer: no child proof discharges a hypothesis of `{lemmaName}`"
    pool := rest
  instantiateMVars (mkAppN lem mvars)

/-- The result of optimizing a subterm: the rewritten `expr` and, when something changed, a proof
that `support <input> = support expr` (`none` means the term is unchanged, i.e. `rfl`). -/
private structure OptResult where
  expr : Expr
  proof? : Option Expr

/-- Compose a chain of optional `support`-equality proofs with `Eq.trans`, dropping the `rfl`
(`none`) links. The shared midpoints are defeq, so `Eq.trans` type-checks across `none` gaps. -/
private def chainProofs (ps : Array (Option Expr)) : MetaM (Option Expr) :=
  ps.foldlM (init := none) fun acc p =>
    match acc, p with
    | none, x => pure x
    | some a, none => pure (some a)
    | some a, some b => some <$> mkEqTrans a b

/-- Does `e` contain a `Gen` — directly, under binders, or in a `List`/`Prod`? Used by the guard in
`optimizeChildren` to tell "nothing to descend into" from "silently skipped a child".

The `List`/`Prod` cases change no answer today (`oneOf`/`frequency` are the only list-carrying heads,
and the guard exempts them by name). They are there so the *next* such combinator trips the guard
instead of slipping past a check that saw `List` at the head and concluded "no `Gen` here". -/
private partial def isGenValued (e : Expr) : MetaM Bool := do
  forallTelescopeReducing (← inferType e) fun _ body => go body
where
  go (ty : Expr) : MetaM Bool := do
    match ty.getAppFn.constName? with
    | some ``Gen => return true
    | some ``List => return (← ty.getAppArgs[0]?.mapM go).getD false
    | some ``Prod => ty.getAppArgs.anyM go
    | _ => return false

/-- The traversal context: the depth binder currently in scope, if any, together with the datatype
whose recursion introduced it. A nested unfold rebinds it to the inner depth — innermost wins. -/
private abbrev Depth := Option (Expr × Name)

mutual

/-- Reduce `e0` (so `match_expr` sees through reducible defs) and optimize it to a fixed point,
returning the rewritten term and a proof that its `support` is unchanged. -/
private partial def optimize (pass : OptPass) (table : Array CongrRule) (depth : Depth) (e0 : Expr) :
    MetaM OptResult := do
  optimizeReduced pass table depth (← withReducible (reduce e0))

/-- Optimize `e`, which is assumed *already reduced*. Optimize children (their subterms are already
reduced too), attempt one head rewrite, and — since a rewrite can introduce new redexes (e.g. the
`pure a >>= f ~> f a` beta) — re-`optimize` (re-reduce) the result. Reducing only here and at the
top avoids re-reducing each subtree once per level of depth. -/
private partial def optimizeReduced (pass : OptPass) (table : Array CongrRule) (depth : Depth)
    (e : Expr) : MetaM OptResult := do
  let cong ← optimizeChildren pass table depth e
  match ← tryHeadRewrite pass depth cong.expr with
  | none => return cong
  | some (e', headPf) =>
    let rest ← optimize pass table depth e'
    let proof? ← chainProofs #[cong.proof?, some headPf, rest.proof?]
    return { expr := rest.expr, proof? }

/-- Descend into a `oneOf`'s branches, rebuilding the choice from the optimized ones.

`oneOf` cannot use the `@[gen_congr]` table: that table rebuilds a node by swapping the arguments it
descended into, but `oneOf`'s nonemptiness proof `h : gs ≠ []` is *dependent* on the branch list, so
a new list paired with the old proof is ill-typed. Hence the by-hand rebuild.

Without this, `optimizeChildren` skipped every `oneOf`, so nothing nested inside a choice's branch
was ever visited — which is why `installTuning` could not reach a choice under a choice. -/
private partial def optimizeOneOfChildren? (pass : OptPass) (table : Array CongrRule) (depth : Depth)
    (e : Expr) : MetaM (Option OptResult) := do
  let_expr Gen.oneOf α gs h := e | return none
  -- The flatten pass builds every branch list with `mkListLit`, so a non-literal one would mean
  -- silently skipping a choice's branches. Throw rather than assert it cannot happen.
  let some elems := listLitElems? gs
    | throwError "optimizer: `oneOf` with a non-literal branch list; cannot descend into\
        {indentExpr gs}"
  if elems.isEmpty then return none
  let rs ← elems.mapM (optimizeReduced pass table depth)
  unless rs.any (·.proof?.isSome) do return none
  let elems' := rs.map (·.expr)
  let genα ← mkAppM ``Gen #[α]
  let gs' ← mkListLit genα elems'
  -- `gs'` is a literal cons, so its nonemptiness is exactly `List.cons_ne_nil`.
  let h' ← mkAppOptM ``List.cons_ne_nil #[genα, elems'.head!, ← mkListLit genα elems'.tail!]
  -- `gs.map support = gs'.map support`, folded from the per-branch proofs. Both lists are literal,
  -- so each `List.map` reduces and the folded proof type-checks against the `map` form by defeq.
  let propTy ← mkArrow α (mkSort .zero)
  let consFn := mkAppN (mkConst ``List.cons [Level.zero]) #[propTy]
  let mut hgMap ← mkEqRefl (← mkListLit propTy [])
  for (g, r) in (elems.zip rs).reverse do
    let pg ← match r.proof? with
      | some p => pure p
      | none   => mkEqRefl (← mkSupport g)
    hgMap ← mkCongr (← mkCongrArg consFn pg) hgMap
  let hg ← mkExpectedTypeHint hgMap
    (← mkEq (← mkAppM ``List.map #[← mkAppOptM ``Gen.support #[α], gs])
            (← mkAppM ``List.map #[← mkAppOptM ``Gen.support #[α], gs']))
  let e' ← mkAppOptM ``Gen.oneOf #[α, gs', h']
  let proof ← mkAppOptM ``support_oneOf_congr #[α, gs, gs', hg, h, h']
  return some { expr := e', proof? := some proof }

/-- Descend into a `frequency`'s branches, rebuilding the choice from the optimized ones.

The `frequency` counterpart of `optimizeOneOfChildren?`, and exempt from the `@[gen_congr]` table for
the same reason: `h : 0 < (gs.map Prod.fst).sum` is *dependent* on the branch list. Weights are
carried through untouched, so `h` retypes at the rebuilt list by defeq — both `List.map Prod.fst`
applications reduce on the literal list to the same sum.

Without this, a hand-written `frequency` in a reducible position was silently skipped, and nothing
nested inside one was ever visited. -/
private partial def optimizeFrequencyChildren? (pass : OptPass) (table : Array CongrRule)
    (depth : Depth) (e : Expr) : MetaM (Option OptResult) := do
  let_expr Gen.frequency α gs h := e | return none
  -- As in `optimizeOneOfChildren?`: a non-literal list would mean silently skipping the branches.
  let some elems := listLitElems? gs
    | throwError "optimizer: `frequency` with a non-literal branch list; cannot descend into\
        {indentExpr gs}"
  if elems.isEmpty then return none
  let pairs ← elems.mapM fun p =>
    match p.getAppFnArgs with
    | (``Prod.mk, #[_, _, w, g]) => pure (w, g)
    | _ => throwError "optimizer: `frequency` branch is not a literal (weight, generator) pair; \
        cannot descend into{indentExpr p}"
  let rs ← pairs.mapM fun (_, g) => optimizeReduced pass table depth g
  unless rs.any (·.proof?.isSome) do return none
  let genα ← mkAppM ``Gen #[α]
  let prodTy ← mkAppM ``Prod #[mkConst ``Nat, genα]
  let pairs' ← (pairs.zip rs).mapM fun ((w, _), r) => mkAppM ``Prod.mk #[w, r.expr]
  let gs' ← mkListLit prodTy pairs'
  -- Weights are unchanged, so `h`'s type at `gs'` is defeq to its type at `gs`. Check it rather
  -- than trusting the reduction silently.
  let hty := (← inferType h).replace fun x => if x == gs then some gs' else none
  unless ← isDefEq (← inferType h) hty do
    throwError "optimizer: rebuilt `frequency` weights do not retype its positivity proof; \
      expected{indentExpr hty}"
  let h' ← mkExpectedTypeHint h hty
  -- `gs.map (fun p => (p.1, support p.2)) = gs'.map …`, folded from the per-branch proofs, exactly
  -- as `optimizeOneOfChildren?` folds its `map support` equality.
  let propTy ← mkArrow α (mkSort .zero)
  let eltTy ← mkAppM ``Prod #[mkConst ``Nat, propTy]
  let consFn := mkAppN (mkConst ``List.cons [Level.zero]) #[eltTy]
  let mut hgMap ← mkEqRefl (← mkListLit eltTy [])
  for ((w, g), r) in (pairs.zip rs).reverse do
    let pg ← match r.proof? with
      | some p => pure p
      | none   => mkEqRefl (← mkSupport g)
    let pairW ← withLocalDeclD `s propTy fun s => do
      mkLambdaFVars #[s] (← mkAppM ``Prod.mk #[w, s])
    hgMap ← mkCongr (← mkCongrArg consFn (← mkCongrArg pairW pg)) hgMap
  let mapFn ← withLocalDeclD `p prodTy fun p => do
    let fst ← mkAppM ``Prod.fst #[p]
    let snd ← mkSupport (← mkAppM ``Prod.snd #[p])
    mkLambdaFVars #[p] (← mkAppM ``Prod.mk #[fst, snd])
  let hg ← mkExpectedTypeHint hgMap
    (← mkEq (← mkAppM ``List.map #[mapFn, gs]) (← mkAppM ``List.map #[mapFn, gs']))
  let e' ← mkAppOptM ``Gen.frequency #[α, gs', h']
  let proof ← mkAppOptM ``support_frequency_congr #[α, gs, gs', hg, h, h']
  return some { expr := e', proof? := some proof }

/-- Optimize the children of `e` and reassemble, proving the result has the same `support` via the
`@[gen_congr]` lemma registered for `e`'s head constant. No head rewrite is attempted here. This
single generic case subsumes every `Gen` constructor and recursion-scheme combinator — except
`oneOf`/`frequency`, whose dependent side-condition proofs it cannot rebuild (see
`optimizeOneOfChildren?` / `optimizeFrequencyChildren?`).

If `e`'s head has no registered congruence lemma, skipping is correct *only* when there is nothing
to descend into; if `e` carries a `Gen`-valued argument we would silently drop an optimization (and
potentially mask synthesis residue), so we fail loudly instead — the fix is to tag that head's
support-congruence lemma `@[gen_congr]`. -/
private partial def optimizeChildren (pass : OptPass) (table : Array CongrRule) (depth : Depth)
    (e : Expr) : MetaM OptResult := do
  if let some r ← optimizeOneOfChildren? pass table depth e then return r
  if let some r ← optimizeFrequencyChildren? pass table depth e then return r
  let some head := e.getAppFn.constName? | return { expr := e, proof? := none }
  -- Under a registered `X.unfold`, the argument we descend into is its step, whose binder 0 is the
  -- recursion's depth.
  let entering := (unfoldNameMap (← getEnv))[head]?
  let some (_, congrName, diff) := table.find? (·.1 == head)
    | do
        -- Compiler-generated eliminators (matchers, recursors) carry Gen-valued arms but are
        -- not descended into structurally; don't flag them.
        let isRec := match (← getEnv).find? head with
          | some (.recInfo _) => true
          | _ => false
        let auxiliary := (← Meta.getMatcherInfo? head).isSome || isRec
        -- The two list-carrying combinators, exempt because neither is actually skipped: each has
        -- a by-hand descent above (`optimizeOneOfChildren?` / `optimizeFrequencyChildren?`) that
        -- reaches this point only by *declining* — i.e. when no branch changed. Both throw rather
        -- than decline on a shape they cannot descend into, so "reached here" really does mean
        -- "nothing to rewrite". Do not widen this exemption to a third combinator without giving
        -- it a descent first.
        let listCarrier := head == ``Gen.oneOf || head == ``Gen.frequency
        -- For any *other* combinator, a Gen-valued argument with no congruence lemma means we would
        -- silently drop an optimization (and could mask synthesis residue): fail loudly instead.
        if !auxiliary && !listCarrier && (← e.getAppArgs.anyM isGenValued) then
          throwError "optimizer: `{head}` has a Gen-valued argument but no `@[gen_congr]` \
            congruence lemma to descend through it; tag its support-congruence lemma `@[gen_congr]`"
        return { expr := e, proof? := none }
  let args := e.getAppArgs
  let mut newArgs := args
  let mut hyps := #[]
  let mut changed := false
  for i in diff do
    let (arg', h?) ← optimizeBinder pass table depth entering args[i]!
    newArgs := newArgs.set! i arg'
    match h? with
    | some h => hyps := hyps.push h; changed := true
    | none   => hyps := hyps.push (← mkBinderRefl args[i]!)
  unless changed do return { expr := e, proof? := none }
  let node' := mkAppN e.getAppFn newArgs
  return { expr := node', proof? := some (← mkCongrProof congrName e node' hyps) }

/-- Optimize a child argument: under any leading binders (`f : dom₁ → … → Gen _`) when it is a
function, or directly when it is a plain `Gen`. Returns the rebuilt argument and, when something
changed, a proof `∀ xs, support (arg xs) = support (arg' xs)`.

`entering` is set when this argument is a registered unfold's step, in which case its binder 0 is
the depth for everything underneath. -/
private partial def optimizeBinder (pass : OptPass) (table : Array CongrRule) (depth : Depth)
    (entering : Option Name) (f : Expr) : MetaM (Expr × Option Expr) := do
  forallTelescope (← inferType f) fun xs _ => do
    let depth :=
      match entering, xs[0]? with
      | some typeName, some d => some (d, typeName)
      | _, _ => depth
    -- `f` is a subterm of an already-reduced node, so `f.beta xs` is reduced (the substituted `xs`
    -- are atomic fvars); descend with `optimizeReduced` to avoid re-reducing it.
    let r ← optimizeReduced pass table depth (f.beta xs)
    let f' ← mkLambdaFVars xs r.expr
    match r.proof? with
    | none => return (f', none)
    | some p => return (f', some (← mkLambdaFVars xs p))

/-- Attempt a single head rewrite on `e`, returning the rewritten term and a proof
`support e = support e'`. -/
private partial def tryHeadRewrite (pass : OptPass) (depth : Depth) (e : Expr) :
    MetaM (Option (Expr × Expr)) := do
  match pass with
  | .flatten distribute => do
    -- Try distribution first: catch `pick x (dite ..)` before `flattenPick?` would bury the choice
    -- in a nested `oneOf`. On success the result is a `dite` whose arms are `pick`s, which the
    -- pass's re-optimization then flattens.
    if distribute then
      if let some r ← distributeChoiceDite? depth e then return some r
    flattenPick? e
  | .installTuning θ st declName => installTuning? θ st declName depth e
  | .main =>
    let res? ←
      match_expr e with
      | bind _ _ _ _ x f => optimizeBind? x f
      | pick _ x y => optimizePick? x y
      | assume _ b f => optimizeAssume? b f
      | _ => pure none
    match res? with
    | none => return none
    | some (e', lemmaName) => return some (e', ← mkLeafProof lemmaName e e')

end

/-- Optimize a raw `Gen` term, returning the optimized term together with a proof that its
`support` equals that of the input. Runs the `.main` (assume-floating / monad-law) pass to a fixed
point first, then the `.flatten` pass, which collapses the `pick` chains the main pass leaves (and
may have extended, via bind-distribution) into single uniform `oneOf` nodes.

Weighting is no longer an optimizer concern: a synthesized generator ships uniform, and
`derive_tuning` makes its weights runtime-addressable after the fact (`installTuning`/`buildTuned`). -/
def optimizeGen (e : Expr) : MetaM (Expr × Expr) := do
  let table := getGenCongrRules (← getEnv)
  let r1 ← optimize .main table none e
  -- Distribute a choice through a `dite` arm (`distributeChoiceDite?`) so each state class's choice is
  -- a flat, per-constructor `oneOf`. This is the shape `derive_tuning` needs to give every constructor
  -- (e.g. STLC's `var`) its own addressable weight; it is support-preserving, and with weighting now
  -- post-hoc there is no reason to withhold it.
  let r2 ← optimize (.flatten true) table none r1.expr
  let expr := r2.expr
  let proof ←
    match ← chainProofs #[r1.proof?, r2.proof?] with
    | some p => mkExpectedTypeHint p (← mkEq (← mkSupport e) (← mkSupport expr))
    | none => mkSupportRefl e
  return (expr, proof)

/-- What `buildTuned` produces: the `θ`-threaded term, its site table, the total branch-slot count,
and the support-preservation proof `installTuning` computes along the way. -/
structure TunedResult where
  /-- `fun (θ : Tuning) args => …`, every `frequency` weight read from `θ`. -/
  tuned : Expr
  /-- The `frequency` sites, in offset-assignment order. -/
  sites : Array TuningSiteInfo
  /-- Total branch slots, i.e. the length of the flat `Tuning.schedules` array. -/
  total : Nat
  /-- `∀ θ args, support (tuned θ args) = support (v args)`, folded from the per-site
  `support_oneOf_reweight` proofs. -/
  supportProof : Expr

/-- From a generator's value `v` (`fun args => X.unfold … seed`), build the `θ`-threaded term
`fun (θ : Tuning) args => …` with its site table, total branch-slot count, and support-preservation
proof. The recursion is the `unfold` combinator, not an `Order.fix` in the term, so it is untouched —
no monotonicity proof to rebuild.

`installTuning` proves `support (oneOf …) = support (frequency …)` at every site
(`support_oneOf_reweight`, parametric in `θ` via `Tuning.weight_pos`); the traversal chains those
into one equation for the whole generator, which `derive_tuning` emits as `gen.tuned_support`. The
direction is flipped here — the pass proves `support v = support tuned`, and the useful statement is
that the *tuned* generator still has the original support. -/
def buildTuned (declName : Name) (v : Expr) : MetaM TunedResult := do
  let table := getGenCongrRules (← getEnv)
  lambdaTelescope v fun args body => do
    withLocalDeclD `θ (mkConst ``Tuning) fun θ => do
      let st ← IO.mkRef ({} : TuningState)
      let r ← optimize (.installTuning θ st declName) table none body
      let state ← st.get
      let tuned ← mkLambdaFVars (#[θ] ++ args) r.expr
      -- `none` means no site fired, so the term is unchanged and the equation is `rfl`.
      let eq ← match r.proof? with
        | some p => mkEqSymm p
        | none   => mkEqRefl (← mkSupport body)
      let supportProof ← mkLambdaFVars (#[θ] ++ args) eq
      return { tuned, sites := state.sites, total := state.nextOffset, supportProof }

end Palamedes
