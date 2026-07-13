import Palamedes.Synthesizer
import Palamedes.Stats
import PalamedesTest.Examples.STLC.WellTyped.WellTyped

/-!
# Spike: depth-indexed weighting for STLC (proposal 09, Phase 2)

The go/no-go question for [proposal 09] is **behavioural**, not proof-theoretic: does replacing the
constant weights that proposal 04 leaves behind with affine, depth-indexed schedules

```
  wⱼ(d) = aⱼ + bⱼ · d        (aⱼ ≥ 1, so every weight is positive at every depth)
```

actually make `genWellTyped []` terminate *and* produce terms worth testing with? Proposal 09's
acceptance criterion 1 is the bar:

> `genWellTyped []` samples without diverging, and its output has median size ≥ 4 with ≥ 70% of
> terms containing at least one application. *Termination alone is not success.*

This file answers that by hand, before any metaprogram exists. It also prototypes the side-goal
that proposal 09 flags as the fiddliest part of `installWeights` (`∀ d, 0 < Σ wⱼ(d)`), and takes
the measurements deferred to Phase 2 by [questions.md Q2] (is the top-heavy shape acceptable?) and
[Q3] (does an uncoupled `arbTy` hurt?).

## What this is a model of, and where it cheats

The shipping design threads the depth as an **argument of `unfoldGo`**, so the seed type is
unchanged and `X.s_unfold`'s `CorrectGen` statement is unchanged. That needs a change to the six
derived `unfold` combinators, which is the bulk of 09's engineering.

This spike instead threads the depth **inside the seed** (`β = Ty × List Ty × Nat`). The two are
distributionally *identical* — `step (τ, Γ, d)` and `step d (τ, Γ)` make the same choices with the
same probabilities — so every number below is the number the real implementation will produce. It
is not the shipping design (a seed-carried depth would change the synthesized predicate, which is
exactly what 09 is at pains to avoid); it is the cheapest thing that yields the numbers.

## The generator being modelled

`WellTyped.genWellTyped`, as synthesized today (`#print` it). Its step generator has **four state
classes**, keyed on the goal type and on whether the context holds a variable of that type.
`unit`/`var` have 0 recursive children, `abs` has 1, `app` has 2, so with the post-04 uniform
weights the mean offspring `m` per class is:

| goal type | var in `Γ`? | branch probabilities                    | mean offspring `m`        |
|-----------|-------------|-----------------------------------------|---------------------------|
| `unit`    | yes         | `unit` ½, `var` ¼, `app` ¼              | `1/2` … subcritical       |
| `unit`    | no          | `unit` ½, `app` ½                       | `1`   … critical          |
| `arrow`   | yes         | `var` ⅓, `abs` ⅓, `app` ⅓               | `1`   … critical          |
| `arrow`   | no          | `abs` ½, `app` ½                        | `3/2` … **supercritical** |

The bottom row is why STLC diverges on ~53% of draws. And it is *reached constantly*: the `app`
rule invents an argument type `a ← arbTy` and hands its children the seeds `(a.arrow τ, Γ)` and
`(a, Γ)`, so every application creates a fresh **arrow** goal for a type that is almost never in
`Γ` — i.e. drops straight into the supercritical class.

**Aside — a live bug for proposal 04.** The `unit`-with-var row is *not* uniform over its three
branches: the synthesized term is `oneOf [pure unit, (dite var-avail (oneOf [var, app]) app)]`, so
`unit` gets ½ where a flat 3-way choice would give it ⅓. The optimizer's `flatten` pass collapses
`pick` *trees*, but here the nesting is under a **`dite`**, which it does not descend through — so
the chain-position skew 04 set out to eliminate survives at this site. It is not what makes STLC
diverge (that is the bottom row), but it is exactly the class of thing 04 claims to have removed,
and it means "every k-way choice is a uniform `oneOf`" is not yet true of the corpus.

**The type is the seed.** That is the mechanism behind Q3, and it is why `arbTy` is not a side
issue: `arbTy` is *itself* a critical branching process today (uniform choice between `unit`, with
0 children, and `arrow`, with 2, so `m = ½·0 + ½·2 = 1` exactly), which makes `E[size(arbTy)]`
**infinite** — and `E[size(arbTy)]` is the constant the term generator's own drift computation
consumes. So this spike fixes `arbTy` too, and measures the two fixes separately.

[proposal 09]: ../../basalt-notes/proposals/09-depth-indexed-weighting.md
[questions.md Q2]: ../../basalt-notes/questions.md
[Q3]: ../../basalt-notes/questions.md
-/

open Palamedes Palamedes.Gen Palamedes.Gen.Support Palamedes.Gen.Total

namespace DepthIndexedSTLC

/-! ## 1. The schedules

A weight schedule per branch, bundled with **the one hypothesis proposal 09's design rule asks
for**: every weight is `≥ 1` at every depth. That hypothesis is what discharges `frequency`'s
positivity side-goal *and* what keeps the support fixed — see §4, where both fall out of it. -/

/-- A depth-indexed weight schedule for the four STLC branches, plus the positivity invariant.

    The design rule — **decay is base-weight *growth*, never recursive-weight shrinkage** — is not
    enforced by the type; `pos` is the part that matters, and it is what every proof below consumes. -/
structure Sched where
  unit : Nat → Nat
  var  : Nat → Nat
  abs  : Nat → Nat
  app  : Nat → Nat
  /-- Proposal 09's `aⱼ ≥ 1`. A recursive weight decaying to `0` would drop its branch from the
      support and destroy completeness; this is the invariant that forbids it. -/
  pos  : ∀ d, 0 < unit d ∧ 0 < var d ∧ 0 < abs d ∧ 0 < app d

/-- **Proposal 09's measured schedules.** `app` (2 recursive children) is held *constant* while the
    closing branches grow with depth, so `m(d)` starts above 1 — big, interesting terms near the
    root — and falls below 1 as the recursion deepens. -/
def affine : Sched where
  unit d := 1 + 30 * d
  var  d := 1 + 30 * d
  abs  d := 1 + 14 * d      -- a lambda is cheap: grows, but slower
  app  _ := 4               -- constant: decayed *relative to* the others, never toward 0
  pos  _ := by omega

/-- 04's uniform weights: what the flattening pass leaves behind today. -/
def uniform : Sched where
  unit _ := 1
  var  _ := 1
  abs  _ := 1
  app  _ := 1
  pos  _ := by omega

/-- [`TUNING-RESEARCH.md` §2.4]'s *certified constant* weights `⟨unit 8, var 8, abs 4, app 1⟩`,
    which clear all four drift constraints with `ε = 1/9`. The notes' claim about them is the whole
    motivation for proposal 09:

    > The resulting generator terminates and is useless. **[measured]** over 3000 draws: median term
    > size 1, 77% are a bare variable or unit, and only 18% contain a single application.

    Reproducing that here is the control the depth-indexed numbers are read against. -/
def certifiedConst : Sched where
  unit _ := 8
  var  _ := 8
  abs  _ := 4
  app  _ := 1
  pos  _ := by omega

/-! ### `arbTy`'s own schedule

`arbTy` is a separate unfold with its **own** depth (proposal 09: *innermost binder wins*). Weights
`[2 + 3d, 1]` give `m = 2/3` at `d = 0` (hence `E[size] = 1/(1 − m) = 3`, proposal 09's target) and
drive `m → 0` with depth, so the tail is thin rather than infinite.

The `d₀` parameter is [Q3]'s knob: `arbTy` reads its schedules at `d₀ + d`, so a call site can hand
it the *enclosing term depth* and get smaller types deeper in the term. `d₀ = 0` (the default)
recovers today's uncoupled behaviour exactly. Q3's decision was to build the knob and leave it off;
this file measures both settings so that decision has numbers under it. -/
def wTyUnit (d : Nat) : Nat := 2 + 3 * d
def wTyArrow (_d : Nat) : Nat := 1

/-- Depth-indexed, subcritical `arbTy`, with [Q3]'s starting-depth knob (default `0` = uncoupled).

    Compare `Palamedes.Gen.arbTy` (`Palamedes/Data/STLC/Ty.lean:29`), which is a uniform `pick` and
    therefore *critical*: `E[size] = ∞`. -/
def arbTyD (d₀ : Nat := 0) : Gen Ty :=
  Ty.unfold
    (fun d => frequency
      [ (wTyUnit d,  pure TyF.unit)
      , (wTyArrow d, pure (TyF.arrow (d + 1) (d + 1))) ]
      (by simp [wTyUnit, wTyArrow]))
    d₀

/-! ## 2. The step generator

A hand-written model of the synthesized step, with the nested `oneOf`s flattened into one
`frequency` per state class and the constant weights replaced by schedules.

`κ` is [Q3]'s coupling coefficient: the `app` rule calls `arbTyD (κ * d)`. `κ = 0` is uncoupled
(today's behaviour, and Q3's default); `κ = 1` is full coupling. -/

/-- The seed: goal type, context, **depth**. In the shipping design the depth is an argument of
    `unfoldGo` and *not* part of the seed; see the module docstring. -/
abbrev Seed := Ty × List Ty × Nat

private def appBranch (κ : Nat) (τ : Ty) (Γ : List Ty) (d : Nat) : Gen (TermF Seed) := do
  let a ← arbTyD (κ * d)
  pure (TermF.app (a.arrow τ, Γ, d + 1) (a, Γ, d + 1))

/-- The step generator, one `frequency` per state class, parameterized by a schedule.

    Every `frequency` here carries the side-goal proposal 09 flags as *"the fiddliest part of the
    metaprogram"*: `0 < Σ wⱼ(d)` with `d` a **free variable**. Each is discharged by
    `simp` + `S.pos d` — i.e. by the design rule alone. That is what `installWeights` would emit;
    see §4. -/
def step (S : Sched) (κ : Nat) : Seed → Gen (TermF Seed)
  | (.unit, Γ, d) =>
    let vars := List.idxsOf Ty.unit Γ
    if h : vars.length > 0 then
      frequency
        [ (S.unit d, pure TermF.unit)
        , (S.var d,  do let i ← Gen.elements vars h; pure (TermF.var i))
        , (S.app d,  appBranch κ .unit Γ d) ]
        (by simp; exact Or.inl (S.pos d).1)
    else
      frequency
        [ (S.unit d, pure TermF.unit)
        , (S.app d,  appBranch κ .unit Γ d) ]
        (by simp; exact Or.inl (S.pos d).1)
  | (.arrow τ₁ τ₂, Γ, d) =>
    let vars := List.idxsOf (τ₁.arrow τ₂) Γ
    if h : vars.length > 0 then
      frequency
        [ (S.var d, do let i ← Gen.elements vars h; pure (TermF.var i))
        , (S.abs d, pure (TermF.abs τ₁ (τ₂, τ₁ :: Γ, d + 1)))
        , (S.app d, appBranch κ (τ₁.arrow τ₂) Γ d) ]
        (by simp; exact Or.inl (S.pos d).2.1)
    else
      frequency
        [ (S.abs d, pure (TermF.abs τ₁ (τ₂, τ₁ :: Γ, d + 1)))
        , (S.app d, appBranch κ (τ₁.arrow τ₂) Γ d) ]
        (by simp; exact Or.inl (S.pos d).2.2.1)

/-- Well-typed term generator at schedule `S`, with [Q3]'s coupling coefficient `κ`. -/
def gen (S : Sched) (κ : Nat) (Γ : List Ty) : Gen Term := do
  let τ ← arbTyD 0
  Term.unfold (step S κ) (τ, Γ, 0)

/-! ## 3. The variants being compared

Isolating the two independent fixes — a subcritical `arbTy`, and depth-indexed term weights — so
they can be attributed separately rather than measured as one lump. -/

/-- **Baseline.** Today's synthesized generator, untouched: uniform weights, *critical* `arbTy`. -/
def genBaseline (Γ : List Ty) : Gen Term := WellTyped.genWellTyped Γ

/-- **Ablation A.** 04's uniform weights, but the subcritical `arbTy`. Isolates the `arbTy` fix. -/
def genUniform (Γ : List Ty) : Gen Term := gen uniform 0 Γ

/-- **Ablation B.** §2.4's certified constants + subcritical `arbTy`. This is the "terminates and is
    useless" control: it should reproduce the notes' median size 1 / ~18% with an application. -/
def genCertifiedConst (Γ : List Ty) : Gen Term := gen certifiedConst 0 Γ

/-- **The proposal.** Depth-indexed weights + subcritical `arbTy`, Q3 coupling **off** (the default). -/
def genAffine (Γ : List Ty) : Gen Term := gen affine 0 Γ

/-- **Q3's knob on.** As above, but `arbTy` inherits the enclosing term depth. -/
def genAffineCoupled (Γ : List Ty) : Gen Term := gen affine 1 Γ

/-! ## 4. The proof obligations

Proposal 09 claims three things go through *unchanged* under depth-indexing. Check them here, on
the real term, before trusting them in a metaprogram. -/

section Obligations

/-! ### The positivity side-goal

`frequency` demands `0 < Σ wⱼ`. With constant weights that is `by decide` on a literal; with
schedules it is universally quantified over a free `d`. Proposal 09 calls this *"the fiddliest part
of the metaprogram"* and says to prototype it on one hand-written example before writing the pass.

**Result: it is not fiddly, and the reason generalizes.** `simp` normalizes
`0 < (List.map Prod.fst [(w₁,_), …, (wₖ,_)]).sum` to the **disjunction** `0 < w₁ ∨ … ∨ 0 < wₖ` —
one disjunct per branch. So the side-goal is discharged by *any single* branch being positive, and
the `aⱼ ≥ 1` design rule hands that over on a plate. `installWeights` does not need to reason about
`d` at all; it emits `simp` followed by picking a disjunct.

Note this is *weaker* than the design rule: positivity of the `frequency` needs only **one** weight
positive, whereas the rule demands **all** of them. The surplus is not wasted — it is exactly what
the support argument below consumes. -/

example (S : Sched) (d : Nat) (g₁ g₂ g₃ : Gen Nat) :
    0 < (([(S.unit d, g₁), (S.var d, g₂), (S.app d, g₃)] : List (Nat × Gen Nat)).map Prod.fst).sum := by
  simp; exact Or.inl (S.pos d).1

example (S : Sched) (d : Nat) (g₁ g₂ : Gen Nat) :
    0 < (([(S.abs d, g₁), (S.app d, g₂)] : List (Nat × Gen Nat)).map Prod.fst).sum := by
  simp; exact Or.inl (S.pos d).2.2.1

/-! ### The correctness lemma: reweighting cannot move the support

This is the single lemma proposal 09 rests `installWeights`' correctness on
(`support_frequency_reweight`). It is proved here in full, and it is what makes `support = P`
survive re-weighting **with the existing proof**.

`support_frequency` already characterizes the support as the union over the *positive-weight*
branches. So for an all-positive `frequency` the weights are invisible to the support, and any two
weightings of the same branch list have the same support. The `aⱼ ≥ 1` rule is exactly the
hypothesis that makes this true — a recursive weight decaying to `0` would silently delete its
branch from the support and destroy completeness. -/

/-- For an all-positive `frequency`, the weights drop out of the support entirely. -/
theorem support_frequency_pos {α : Type} {gs : List (Nat × Gen α)} (h) (hpos : ∀ p ∈ gs, 0 < p.1) :
    support (frequency gs h) = fun a => ∃ g ∈ gs.map Prod.snd, support g a := by
  rw [support_frequency]
  funext a
  apply propext
  constructor
  · rintro ⟨w, g, hmem, _, ha⟩
    exact ⟨g, List.mem_map.mpr ⟨(w, g), hmem, rfl⟩, ha⟩
  · rintro ⟨g, hmem, ha⟩
    obtain ⟨⟨w, g'⟩, hmem', hg⟩ := List.mem_map.mp hmem
    cases hg
    exact ⟨w, g', hmem', hpos _ hmem', ha⟩

/-- **Proposal 09's `support_frequency_reweight`.** Two all-positive weightings of the same branch
    list induce the same support. This is the whole correctness argument for `installWeights`. -/
theorem support_frequency_reweight {α : Type} {gs gs' : List (Nat × Gen α)}
    (hsnd : gs.map Prod.snd = gs'.map Prod.snd)
    (hpos : ∀ p ∈ gs, 0 < p.1) (hpos' : ∀ p ∈ gs', 0 < p.1) (h) (h') :
    support (frequency gs h) = support (frequency gs' h') := by
  rw [support_frequency_pos h hpos, support_frequency_pos h' hpos', hsnd]

/-! **Why the *instantiation* of this lemma at `step` is not stated here.** In the shipping design
the depth is an argument of `unfoldGo`, so a branch's child seeds do not mention `d` and
`support (step d x) = support (step d' x)` is `support_frequency_reweight` applied once per site.
In *this spike* the depth rides inside the seed (see the module docstring), so the branch
generators at depth `d` and `d'` are genuinely different terms — they emit different child seeds —
and the statement is not even type-correct as an equality of supports over `Seed`. That is an
artifact of the shortcut, not of the design. The lemma above is the real content, and it is proved. -/

/-! ### Totality survives (proposal 09, acceptance criterion 3) -/

@[simp, aesop safe (rule_sets := [totality])]
theorem total_arbTyD (d₀ : Nat) : (arbTyD d₀).total := by
  apply Ty.total_unfold
  intro _
  totality

theorem total_step (S : Sched) (κ : Nat) (s : Seed) : (step S κ s).total := by
  obtain ⟨τ, Γ, d⟩ := s
  cases τ <;> simp only [step] <;> split <;> totality

theorem total_gen (S : Sched) (κ : Nat) (Γ : List Ty) : (gen S κ Γ).total := by
  apply total_bind (total_arbTyD 0)
  intro _
  exact Term.total_unfold (total_step S κ)

end Obligations

/-! ## 5. Measurement

`#genstats`' rendered report answers "what does the distribution look like", but proposal 09's
acceptance criteria are specific predicates ("median size ≥ 4", "≥ 70% contain an application"),
so we compute them directly off `GenStats.runDraws` rather than eyeballing a histogram. -/

section Measure

/-- Structural size: number of `Term` constructors. -/
def Term.size : Term → Nat
  | .unit | .var _ => 1
  | .abs _ t => 1 + Term.size t
  | .app t₁ t₂ => 1 + Term.size t₁ + Term.size t₂

def Term.hasApp : Term → Bool
  | .unit | .var _ => false
  | .abs _ t => Term.hasApp t
  | .app _ _ => true

/-- Total size of every type annotation in the term — the Q3 observable. An uncoupled `arbTy`
    should make this grow with term size; a coupled one should hold it down. -/
def Term.tySize : Ty → Nat
  | .unit => 1
  | .arrow a b => 1 + Term.tySize a + Term.tySize b

def Term.annotSize : Term → Nat
  | .unit | .var _ => 0
  | .abs τ t => Term.tySize τ + Term.annotSize t
  | .app t₁ t₂ => Term.annotSize t₁ + Term.annotSize t₂

/-- Per-depth node census: `(nodes at depth i, apps at depth i)`. This is [Q2]'s measurement — the
    top-heaviness of the generated shape. -/
def Term.censusAux : Term → Nat → Array (Nat × Nat) → Array (Nat × Nat)
  | t, d, acc =>
    let acc := if acc.size ≤ d then acc.push (0, 0) else acc
    let (n, a) := acc[d]!
    let isApp := match t with | .app _ _ => 1 | _ => 0
    let acc := acc.set! d (n + 1, a + isApp)
    match t with
    | .unit | .var _ => acc
    | .abs _ t' => Term.censusAux t' (d + 1) acc
    | .app t₁ t₂ => Term.censusAux t₂ (d + 1) (Term.censusAux t₁ (d + 1) acc)

def Term.census (t : Term) : Array (Nat × Nat) := Term.censusAux t 0 #[]

private def pct (n k : Nat) : String :=
  if k == 0 then "—" else
    let x := (n * 1000) / k
    s!"{x / 10}.{x % 10}%"

private def median (xs : Array Nat) : Nat :=
  if xs.isEmpty then 0 else (xs.qsort (· < ·))[xs.size / 2]!

private def quantile (xs : Array Nat) (num den : Nat) : Nat :=
  if xs.isEmpty then 0 else
    let s := xs.qsort (· < ·)
    s[min (s.size - 1) (s.size * num / den)]!

private def mean10 (xs : Array Nat) : String :=
  if xs.isEmpty then "—" else
    let m := (xs.foldl (· + ·) 0 * 10) / xs.size
    s!"{m / 10}.{m % 10}"

/-- Run a generator and report proposal 09's acceptance criteria directly. -/
def measure (label : String) (g : Gen Term) (draws := 3000) (fuel := 10000) : IO Unit := do
  let results := GenStats.runDraws (toStatGen g) { draws, fuel, seed := 0 }
  let mut ok : Array Term := #[]
  let mut outOfFuel := 0
  let mut failed := 0
  for r in results do
    match r with
    | .ok (t, _) => ok := ok.push t
    | .error .outOfFuel => outOfFuel := outOfFuel + 1
    | .error (.failure _) => failed := failed + 1
  let sizes := ok.map Term.size
  let withApp := ok.filter Term.hasApp |>.size
  let trivial := ok.filter (fun t => Term.size t ≤ 2) |>.size
  let annots := ok.map Term.annotSize
  -- Q2: application rate by depth, aggregated over the corpus.
  let mut census : Array (Nat × Nat) := #[]
  for t in ok do
    for (i, (n, a)) in (Term.census t).toList.zipIdx.map (fun (x, i) => (i, x)) do
      if census.size ≤ i then census := census.push (0, 0)
      let (n', a') := census[i]!
      census := census.set! i (n' + n, a' + a)
  IO.println s!"── {label}  ({draws} draws, fuel {fuel})"
  IO.println s!"   divergences (fuel-exhausted)   {outOfFuel}  ({pct outOfFuel draws})"
  IO.println s!"   failures                       {failed}"
  IO.println s!"   term size     mean {mean10 sizes}   p50 {median sizes}   \
p95 {quantile sizes 95 100}   max {sizes.foldl max 0}"
  IO.println s!"   ≥ 1 application                {pct withApp ok.size}   [09 wants ≥ 70%]"
  IO.println s!"   trivial (≤ 2 nodes)            {pct trivial ok.size}"
  IO.println s!"   type-annotation size  mean {mean10 annots}   max {annots.foldl max 0}   [Q3]"
  IO.print   s!"   app rate by depth [Q2]        "
  for (i, (n, a)) in census.toList.zipIdx.map (fun (x, i) => (i, x)) do
    if i < 8 then IO.print s!" d{i}:{pct a n}"
  IO.println ""
  IO.println ""

end Measure

/-! ## 6. Results -/

#eval measure "BASELINE  today's genWellTyped (uniform weights, critical arbTy)" (genBaseline [])
#eval measure "ABLATION A  uniform weights + subcritical arbTy" (genUniform [])
#eval measure "ABLATION B  §2.4 certified constants ⟨8,8,4,1⟩ + subcritical arbTy" (genCertifiedConst [])
#eval measure "PROPOSAL 09  depth-indexed, κ = 0 (uncoupled arbTy — Q3's default)" (genAffine [])
#eval measure "Q3 KNOB ON  depth-indexed, κ = 1 (arbTy inherits term depth)" (genAffineCoupled [])

end DepthIndexedSTLC
