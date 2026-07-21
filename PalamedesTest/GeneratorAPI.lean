/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Synthesizer
import Palamedes.Data.List
import Palamedes.Data.Nat
import Palamedes.Sample
import Palamedes.Stats

/-!
# The generator API: one vocabulary across Basalt and Palamedes

`generator_search` dispatches on the **declared return type**: whether a generator can fail is a
fact about its type, visible at every use site.

| totality | declared | result |
|---|---|---|
| succeeds | `G α` | emitted from the `TGen` witness |
| filters | `G (Option α)` | emitted via `totalize` |
| filters | `G α` | error — declare `G (Option α)` |
| succeeds | `G (Option α)` | warning — it never fails, `G α` will do |
| *gap* | either | error / warning naming the **basis gap**, never advising `Option` |

The last row is a third totality outcome, distinct from "filters": reconstruction can come up empty
because the generator genuinely filters, or because the basis could not cover it. Only the first is
a fact about the generator. See `diagnoseTotality` (`Synthesizer/FrontEnd.lean`) and the section at
the bottom of this file.
-/

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

/-! ## Row 1 — total, declared total: a Basalt generator, no wrapper -/

def genAllTwos [Gen G] : G (List Nat) := by
  generator_search (fun xs => isAllTwos xs)

-- It is a Basalt generator, so Basalt's own tooling takes it directly — no adapter, no `.run`.
/--
info: genAllTwos — 30 draws (seed 0, fuel 10000)

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
-/
#guard_msgs in
#genstats (draws := 30) genAllTwos

/-! ## Row 2 — filtering, declared filtering: emitted via `totalize` -/

def genBetween (lo hi : Nat) [Gen G] : G (Option Nat) := by
  generator_search (fun n => lo ≤ n ∧ n ≤ hi)

-- Already `Option`-reflected by its type, so it samples through the retry loop directly.
#eval show IO Unit from do
  let n ← Palamedes.samplePartial (genBetween 3 7)
  unless 3 ≤ n && n ≤ 7 do
    throw <| IO.userError s!"genBetween produced {n}, outside [3,7]"

/-! ## Row 3 — filtering, declared total: an error, naming the fix

`G α` is `Fail`-free by construction, so there is no term to emit — hence an error, not a warning.
A warning is only implementable for the synthesis-internal `Palamedes.PGen α` carrier (row 5), where
a filtering term *does* exist. -/

/--
error: generator_search: this generator filters — a `PGen.assume` survived optimization — so it cannot be emitted at
  G ℕ, which is `Fail`-free by construction.

Declare it as `G (Option _)` instead, so the type reflects that it can fail.
-/
#guard_msgs in
example (lo hi : Nat) [Gen G] : G Nat := by
  generator_search (fun n => lo ≤ n ∧ n ≤ hi)

/-! ## Row 4 — total, declared filtering: a hint, and the generator still works

The `Option` is not wrong, only unnecessary — there is a term to emit (via `totalize`), so unlike
row 3 this stays a warning. -/

/--
warning: this generator never fails, so the `Option` is not needed — `G (List ℕ)` will do.
-/
#guard_msgs in
def genAllTwosOpt [Gen G] : G (Option (List Nat)) := by
  generator_search (fun xs => isAllTwos xs)

/-! ## Row 5 — filtering, declared at the `Palamedes.PGen α` carrier: a warning

The carrier is not `Fail`-free, so a filtering term *does* exist and can be emitted — hence a
warning where row 3's Basalt `G α` is an error. This is the only row that fires on the carrier
shape, and no corpus generator is declared this way any more, so without this case the branch is
unreachable from the whole build.
-/

/--
warning: this generator filters: a `PGen.assume` survived optimization, so it can fail when sampled. Declare it as `[Gen G] → G (Option _)` to reflect that in the type.
-/
#guard_msgs in
def genBetweenCarrier (lo hi : Nat) : Palamedes.PGen Nat := by
  generator_search (fun n => lo ≤ n ∧ n ≤ hi)

-- The warning is a hint, not a rejection: the generator is emitted and filters as advertised.
#eval show IO Unit from do
  let n ← Palamedes.samplePartial (Palamedes.PGen.totalize (genBetweenCarrier 3 7))
  unless 3 ≤ n && n ≤ 7 do
    throw <| IO.userError s!"genBetweenCarrier produced {n}, outside [3,7]"

/-! ## `classifyGoal` rejects goals it cannot read

Three ways a goal fails to name a generator. Each is a message about the *declaration*, which is the
point: the alternative is a mismatch surfacing later from inside the emitted `totalize`/`TGen.run`,
which reads as a bug in emission rather than a fact about what was declared.
-/

-- A predicate whose domain is not the goal's element type.
/--
error: generator_search: the predicate must have type
  ℕ → Prop
-/
#guard_msgs in
example : Palamedes.PGen Nat := by generator_search (fun xs => isAllTwos xs)

-- A goal whose type constructor has no Basalt `Gen` instance.
/--
error: generator_search: the goal's type constructor
  List
is not a Basalt generator monad (no `Gen` instance), and the goal is not `Palamedes.PGen α`
-/
#guard_msgs in
example : List Nat := by generator_search (fun n => n = 2)

/-! ## The predicate, not the goal, picks the reading

For a `G (Option β)` goal the filtering reading is tried first, because that is what the shape exists
to express. Elaborating against an expected type is too permissive to decide it the other way round:
`fun n => 3 ≤ n ∧ n ≤ 7` typechecks at `Option Nat → Prop` as well, since Mathlib gives `Option` an
`LE` instance and silently coerces `3` to `some 3`. Trying `Option Nat` first is what made
`genBetweenLoAndHi` synthesize against `fun n => some lo ≤ n ∧ n ≤ some hi`.

A predicate genuinely over `Option β` stays reachable by annotating its binder
(`fun (o : Option β) => …`), which makes the `β → Prop` attempt fail and falls through to the total
reading. There is **no test for that path here, because no such generator is currently
synthesizable**: `Option` is not a `derive_palamedes`'d datatype, so the search has no rules for it
and `CorrectGen (P : Option β → Prop)` cannot be solved regardless of dispatch. The escape hatch is
worth keeping, but the ambiguity it guards against is latent rather than live.
-/

/-! ## A missing witness is not the same claim as "it filters"

`totality` is `repeat' first | …`, and `repeat'` does not fail — so a datatype with no `@[total]`
lemma does not throw, it simply leaves goals, exactly like a generator that genuinely filters.
Control flow alone cannot separate them, and reading the empty result as "it filters" sends the user
to add an `Option` their generator does not need. `totalize` accepts it, the "never fails" check is
silent (it keys on a witness that is absent either way), and the law emitted for the declaration
weakens from `IsSoundAndComplete` to `IsSomeSoundAndComplete`. The bad diagnosis is actionable, the
action succeeds, and the evidence is buried.

So `diagnoseTotality` reads the *term* as well: `PGen.assume` is the only thing a generator can fail
at, and the optimizer floats every satisfiable one out, so no `assume` anywhere means "it filters"
is not a claim the evidence supports. The corpus covers the `.filters` rows — five filtering
generators synthesize without a spurious warning — but nothing in it reaches a basis gap, so the
three cases are pinned directly. -/

private def mkRes (gen : Lean.Expr) (err? : Option Lean.MessageData) : SynthesisResult :=
  { gen, supportProof := Lean.mkConst ``Nat.zero, totalWitness? := none, totalityFailure? := err? }

private def diagnosisLabel : TotalityDiagnosis → String
  | .filters => "filters"
  | .gap none => "gap (left goals, no assume)"
  | .gap (some _) => "gap (errored)"

/-- info: "filters" -/
#guard_msgs in
#eval diagnosisLabel (diagnoseTotality (mkRes (Lean.mkConst ``Palamedes.PGen.assume) none))

/-- info: "gap (left goals, no assume)" -/
#guard_msgs in
#eval diagnosisLabel (diagnoseTotality (mkRes (Lean.mkConst ``Nat.zero) none))

-- A thrown error is a gap whatever the term contains: it is not an answer about the generator.
/-- info: "gap (errored)" -/
#guard_msgs in
#eval diagnosisLabel
  (diagnoseTotality (mkRes (Lean.mkConst ``Palamedes.PGen.assume) (some m!"boom")))
