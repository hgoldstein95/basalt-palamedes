/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Synthesizer
import Palamedes.Data.List
import Palamedes.Data.Nat
import Palamedes.Sample
import PalamedesTest.Harness

/-!
# Tuning regression: a `Tuning` binder is threaded through synthesis

**The signature says whether a generator is tunable.** A `θ : Tuning` binder in scope is threaded
through every choice site by `installTuning`, run inside the pipeline between optimize and totality;
no binder means the generator ships uniform. There is no command and no flag.

Two properties carry the design, and both are pinned below:

* **One generator, one law.** `sound_complete` is `∀ … θ, …` because `θ` is one of the
  declaration's own binders, so the support invariant across every weighting is the *ordinary* law
  rather than a separate `tuned_support`/`tuned_sound_complete` pair. Nothing here relates two
  independently-derived generators, so there is no fidelity check to perform.
* **`.uniform` is universal.** `Tuning.weight` reads `θ.schedules.getD i (1, 0)`, so the empty
  tuning is the uniform weighting of *any* generator. That is what lets `(θ : Tuning := .uniform)`
  be written before the site count is known, and what makes the untuned call site mention tuning
  nowhere.
-/

open Palamedes

namespace PalamedesTest.Tuning

@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

/-! ## No `Tuning` binder is a legitimate signature: uniform, and no site table -/

def genUntuned [Gen G] : G (List Nat) := by generator_search (fun xs => isAllTwos xs)

run_cmd
  PalamedesTest.assertNotDeclared `PalamedesTest.Tuning.genUntuned.sites
    "genUntuned declared no `Tuning` binder, so it ships uniform"

/-! ## The total shape, tuned in place

There is no companion generator and no re-projection: the generator is tuned *before* it is
packaged, so the `TGen` witness is built once, over the θ-open term. `total_frequency` never
inspects weights, which is why stage 4 closes exactly as it does for a uniform generator. -/

/--
info: @[correct] PalamedesTest.Tuning.genLawful: emitted sound_complete
-/
#guard_msgs in
@[correct] def genLawful (θ : Tuning := .uniform) [Gen G] : G (List Nat) := by
  generator_search (fun xs => isAllTwos xs)

/--
info: @genLawful.sound_complete : ∀ (θ : optParam Tuning Tuning.uniform),
  IsSoundAndComplete (genLawful θ) fun xs => isAllTwos xs = true
-/
#guard_msgs in
#check @genLawful.sound_complete
/--
info: 'PalamedesTest.Tuning.genLawful.sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms genLawful.sound_complete

-- The site table `installTuning` emitted, and a policy materialized against it.
/--
info: #[{ name := `PalamedesTest.Tuning.genLawful.site0, offset := 0, arity := 2, holes := #[0, 1] }]
-/
#guard_msgs in
#eval genLawful.sites
/--
info: { schedules := #[(1, 12), (3, 0)] }
-/
#guard_msgs in
#eval SchedulePolicy.moderate.materialize genLawful.sites

-- The law is usable at any weighting, from the one theorem.
example (P : List Nat → Prop) (hP : (fun xs => isAllTwos xs = true) = P) (θ : Tuning) :
    IsSoundAndComplete (genLawful θ (G := SPMF)) P := by
  rw [← hP]; exact genLawful.sound_complete θ

/--
info: genLawful — 30 draws (seed 0, fuel 10000)

  outcomes    ok 30 (100.0%)
  size        mean 1.8   p50 1   p95 4   max 5
  choices     mean 1.8   p50 1   p95 4   max 5
  distinct    5 / 30

  head constructor
    nil     53.3%  (16)
    cons    46.7%  (14)

  most common
     53.3%  (16)  []
     23.3%   (7)  [2]
     13.3%   (4)  [2, 2]
      6.7%   (2)  [2, 2, 2]

  samples
    [2, 2]
    []
    []

  laws: sound_complete ✓
        terminates      — (not proved; measured 0/30 divergences)
        cost_bounded    — (not proved)
        filter_free     — (not proved)
        productive      — (not proved)
-/
#guard_msgs in
#genstats (draws := 30) genLawful
/--
info: (genLawful (SchedulePolicy.moderate.materialize genLawful.sites)) — 30 draws (seed 0, fuel 10000)

  outcomes    ok 30 (100.0%)
  size        mean 1.9   p50 2   p95 3   max 3
  choices     mean 1.9   p50 2   p95 3   max 3
  distinct    3 / 30

  head constructor
    cons    73.3%  (22)
    nil     26.7%   (8)

  most common
     56.7%  (17)  [2]
     26.7%   (8)  []
     16.7%   (5)  [2, 2]

  samples
    [2, 2]
    [2, 2]
    []

  laws: sound_complete ✓
        terminates      — (not proved; measured 0/30 divergences)
        cost_bounded    — (not proved)
        filter_free     — (not proved)
        productive      — (not proved)
-/
#guard_msgs in
#genstats (draws := 30) (genLawful (SchedulePolicy.moderate.materialize genLawful.sites))

/-! ## A tuned generator still prints as a generator

The pin below is on the *emitted term*, and specifically on the `frequency` branch list appearing
with no side-condition argument after it. `delabDroppingProof` drops that argument only when the
combinator's autoParam can rebuild it, and a tuned generator's weights are `Tuning.weight θ i d` —
opaque in `θ`, so the goal `0 < Σ wⱼ(d)` reduces to `0 < θ.weight 0 d ∨ …` and stops unless
`Tuning.weight_pos` is available to `simp`. Untag it (`Schedule.lean`) and this term regrows a
~25-line `Eq.trans`/`congrArg` tower over `TGen.frequency._proof_1`. That is the one printing hazard
a tuning binder introduces, and only a pin on a *tuned* generator can see it — this one and
`genWellTyped`, the corpus's other tuned pin. -/

/--
info: Try this:
  [apply] exact
    List.unfoldGo
      (fun d x => do
        let a ←
          frequency
              [(Tuning.weight θ 0 d, fun x => pure ListF.nil),
                (Tuning.weight θ 1 d, fun x => pure (ListF.cons 2 PUnit.unit))]
        match a with
          | ListF.nil => pure ListF.nil
          | ListF.cons a1 a2 => pure (ListF.cons a1 (a2, PUnit.unit)))
      0 (PUnit.unit, PUnit.unit)
-/
#guard_msgs in
def genPinned (θ : Tuning := .uniform) [Gen G] : G (List Nat) := by
  generator_search? (fun xs => isAllTwos xs)

/-! ## The filtering shape

Declared **without** a `Tuning` binder, and that is not an oversight. This generator synthesizes to
an `assume` over a `choose` with no `oneOf` anywhere, so there is no choice site for a `θ` to reach
and the binder would be dead — Lean's own unused-variable linter says so, which is the right tool
reporting it.

Filtering *and* branching is covered by `Corpus/Tree/AVL/AVL.lean`, which tags the recursive
filtering `genAVL`. That combination is the one that stresses the `someSupport` bridge: reaching the
twins there means case-splitting the step generator's nested conditionals, not merely having a twin
for each combinator. See `Synthesizer/Correct.lean`. -/

/--
info: @[correct] PalamedesTest.Tuning.genRange: emitted sound_complete
-/
#guard_msgs in
@[correct] def genRange (lo hi : Nat) [Gen G] : G (Option Nat) := by
  generator_search (fun n => lo ≤ n ∧ n ≤ hi)

run_cmd
  PalamedesTest.assertNotDeclared `PalamedesTest.Tuning.genRange.sites
    "genRange has no choice sites to tune"

/--
info: genRange.sound_complete : ∀ (lo hi : ℕ), IsSomeSoundAndComplete (genRange lo hi) fun n => lo ≤ n ∧ n ≤ hi
-/
#guard_msgs in
#check @genRange.sound_complete
/--
info: 'PalamedesTest.Tuning.genRange.sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms genRange.sound_complete

#eval show IO Unit from do
  let n ← Palamedes.samplePartial (genRange 3 7)
  unless 3 ≤ n && n ≤ 7 do throw <| IO.userError s!"genRange produced {n}, outside [3,7]"

/-! ## Binder order

`θ` is found by *type*, so it can sit anywhere in the telescope — including after `[Gen G]`, which
`declBinders` and `forallTelescope` both order the same way. -/

/--
info: @[correct] PalamedesTest.Tuning.genFlip: emitted sound_complete
-/
#guard_msgs in
@[correct] def genFlip [Gen G] (_n : Nat) (θ : Tuning := .uniform) : G (List Nat) := by
  generator_search (fun xs => isAllTwos xs)

/--
info: @genFlip.sound_complete : ∀ (_n : ℕ) (θ : optParam Tuning Tuning.uniform),
  IsSoundAndComplete (genFlip _n θ) fun xs => isAllTwos xs = true
-/
#guard_msgs in
#check @genFlip.sound_complete

end PalamedesTest.Tuning
