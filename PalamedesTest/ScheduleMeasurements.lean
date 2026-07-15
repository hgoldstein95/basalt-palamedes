import Palamedes.Synthesizer
import Palamedes.Stats
import PalamedesTest.Examples.STLC.WellTyped.WellTyped

/-!
# Regression test for depth-indexed weight schedules (`with_schedules`)

The guard on `installWeights` and on `decayPolicy`'s hand-tuned coefficients — nothing else pins
them, so this file is what notices if they are retuned. The bar: sample without diverging, median
term size ≥ 4, and ≥ 70% of terms containing an application. **Termination alone is not success** —
a generator that decays too fast terminates by emitting nothing but leaves.

`#genstats` covers outcomes and size. `measureShape` below adds the four things it cannot express,
all domain-specific: whether an `app` occurs *anywhere* (the histogram sees head constructors only),
the fraction of trivial terms, the total size of type annotations, and the per-depth application
rate.

**Keep this file free of proofs.** It is all `#eval`/`#genstats`, which re-run on every elaboration,
so a generator that regresses into diverging makes every draw burn its full fuel budget and this file
take minutes.
-/

open Palamedes Palamedes.Gen

/-! ## Outcomes and size — `#genstats`, pinned

`arbTy` used to be a critical branching process (`m = 1` exactly, so `E[size] = ∞`; measured mean
711, max 93,857). It is now subcritical, and this is where that shows. -/

/--
info: (toStatGen arbTy) — 3000 draws (seed 0, fuel 10000)

  outcomes    ok 3000 (100.0%)
  size        mean 1.9   p50 1   p95 5   max 13
  choices     mean 1.9   p50 1   p95 5   max 13
  distinct    27 / 3000

  head constructor
    unit     67.4%  (2023)
    arrow    32.6%   (977)

  most common
     67.4%  (2023)  Ty.unit
     22.4%   (673)  Ty.arrow (Ty.unit) (Ty.unit)
      3.6%   (109)  Ty.arrow (Ty.arrow (Ty.unit) (Ty.unit)) (Ty.unit)
      3.5%   (106)  Ty.arrow (Ty.unit) (Ty.arrow (Ty.unit) (Ty.unit))
      0.5%    (16)  Ty.arrow (Ty.arrow (Ty.unit) (Ty.unit)) (Ty.arrow (Ty.unit) (Ty.unit))

  samples
    Ty.arrow (Ty.unit) (Ty.unit)
    Ty.unit
    Ty.unit
-/
#guard_msgs in
#genstats (draws := 3000) (fuel := 10000) (toStatGen arbTy)

/-! Before schedules, `genWellTyped` diverged on 54.3% of draws and its median output was a single
node. The `outcomes` and `size` lines below are the bar it now has to clear.

The distribution's sharper tell is `var`. The `unit`-goal state's choice is `unit` against a `dite`
on whether a variable of the goal type is in context, with `var`/`app` chosen inside it. That choice
is now distributed *through* the `dite` (`distributeChoiceDite?` in the optimizer), so `unit`, `var`,
and `app` sit in a single flat `oneOf` and each carries its own schedule — `var` and `unit` a leaf
weight (`1 + 30d`), `app` the constant recursive weight `4`. So `var` is a live option wherever a
variable is available: the `most common` table splits the old single `app (abs unit unit) unit` into
a `unit`-bodied and a `var 0`-bodied form, and `distinct` rises (496 → 666). While `var` was buried
in the `dite` it split the branch 50/50 with `app` at a flat rate; freeing it restores the intended
per-depth curve (`d2` 6.7% → 7.6%, back to proposal 09's prototype numbers). The head-constructor
distribution is a depth-0 effect and is untouched. -/

/--
info: (toStatGen (WellTyped.genWellTyped [])) — 3000 draws (seed 0, fuel 10000)

  outcomes    ok 3000 (100.0%)
  size        mean 5.6   p50 5   p95 12   max 26
  choices     mean 10.3   p50 9   p95 23   max 51
  distinct    666 / 3000

  head constructor
    app     80.3%  (2408)
    unit    13.3%   (398)
    abs      6.5%   (194)

  most common
     13.3%  (398)  Term.unit
     12.2%  (367)  Term.app (Term.abs (Ty.unit) (Term.unit)) (Term.unit)
     11.8%  (354)  Term.app (Term.abs (Ty.unit) (Term.var 0)) (Term.unit)
      3.6%  (108)  Term.app (Term.abs (Ty.arrow (Ty.unit) (Ty.unit)) (Term.unit)) (Term.abs (Ty.unit) (Term.…
      3.3%   (98)  Term.app (Term.abs (Ty.arrow (Ty.unit) (Ty.unit)) (Term.unit)) (Term.abs (Ty.unit) (Term.…

  samples
    Term.abs (Ty.unit) (Term.var 0)
    Term.app (Term.abs (Ty.arrow (Ty.unit) (Ty.arrow (Ty.unit) (Ty.unit))) (Term.unit)) (Term…
    Term.app (Term.abs (Ty.arrow (Ty.unit) (Ty.unit)) (Term.unit)) (Term.abs (Ty.unit) (Term.…
-/
#guard_msgs in
#genstats (draws := 3000) (fuel := 10000) (toStatGen (WellTyped.genWellTyped []))

/-! ## The four STLC-specific observables `#genstats` cannot express -/

namespace ScheduleMeasurements

def Ty.size : Ty → Nat
  | .unit => 1
  | .arrow a b => 1 + Ty.size a + Ty.size b

def Term.size : Term → Nat
  | .unit | .var _ => 1
  | .abs _ t => 1 + Term.size t
  | .app t₁ t₂ => 1 + Term.size t₁ + Term.size t₂

/-- Does an application occur anywhere in the term? -/
def Term.hasApp : Term → Bool
  | .unit | .var _ => false
  | .abs _ t => Term.hasApp t
  | .app _ _ => true

/-- Total size of every type annotation. This is where a critical `arbTy` used to show up: mean 73.0,
with a single term once carrying a 9,867-node type. -/
def Term.annotSize : Term → Nat
  | .unit | .var _ => 0
  | .abs τ t => Ty.size τ + Term.annotSize t
  | .app t₁ t₂ => Term.annotSize t₁ + Term.annotSize t₂

/-- Per-depth node census, `(nodes at depth i, apps at depth i)`. This is what depth decay costs:
applications end up concentrated near the root, and how top-heavy is too top-heavy is still open. -/
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

private def pct (n k : Nat) : String :=
  if k == 0 then "—" else
    let x := (n * 1000) / k
    s!"{x / 10}.{x % 10}%"

private def mean10 (xs : Array Nat) : String :=
  if xs.isEmpty then "—" else
    let m := (xs.foldl (· + ·) 0 * 10) / xs.size
    s!"{m / 10}.{m % 10}"

/-- The observables that do not fit `#genstats`' report. Outcomes and the size distribution are not
recomputed here — read them off the `#genstats` output above.

TODO: Consider upstreaming more generic infrastructure to Basalt to support this kind of thing. -/
def measureShape (g : Palamedes.Gen Term) (draws := 3000) (fuel := 10000) : IO Unit := do
  let ok := (GenStats.runDraws (toStatGen g) { draws, fuel, seed := 0 }).filterMap
    fun | .ok (t, _) => some t | .error _ => none
  let withApp := ok.filter Term.hasApp |>.size
  let trivial := ok.filter (fun t => Term.size t ≤ 2) |>.size
  let annots := ok.map Term.annotSize
  let mut census : Array (Nat × Nat) := #[]
  for t in ok do
    for (i, (n, a)) in (Term.censusAux t 0 #[]).toList.zipIdx.map (fun (x, i) => (i, x)) do
      if census.size ≤ i then census := census.push (0, 0)
      let (n', a') := census[i]!
      census := census.set! i (n' + n, a' + a)
  IO.println s!"── shape of {ok.size} completed draws"
  IO.println s!"   ≥ 1 application      {pct withApp ok.size}   [want ≥ 70%]"
  IO.println s!"   trivial (≤ 2 nodes)  {pct trivial ok.size}"
  IO.println s!"   type-annotation size  mean {mean10 annots}   max {annots.foldl max 0}"
  IO.print   s!"   app rate by depth    "
  for (i, (n, a)) in census.toList.zipIdx.map (fun (x, i) => (i, x)) do
    if i < 8 then IO.print s!" d{i}:{pct a n}"
  IO.println ""

/--
info: ── shape of 3000 completed draws
   ≥ 1 application      80.9%   [want ≥ 70%]
   trivial (≤ 2 nodes)  18.2%
   type-annotation size  mean 3.6   max 32
   app rate by depth     d0:80.2% d1:17.7% d2:7.6% d3:5.3% d4:3.7% d5:2.8% d6:1.1% d7:0.9%
-/
#guard_msgs in
#eval measureShape (WellTyped.genWellTyped [])

end ScheduleMeasurements
