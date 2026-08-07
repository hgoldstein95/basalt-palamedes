/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Synthesizer
import Palamedes.Data.List
import Palamedes.Data.Nat
import Palamedes.Sample

/-!
# The generator API: one vocabulary across Basalt and Palamedes

`generator_search` dispatches on the **declared return type**: whether a generator can fail is a
fact about its type, visible at every use site. Both declarable shapes are Basalt's — there is no
Palamedes-flavoured third one, so a synthesized generator is always something Basalt's own tooling
consumes with no adapter.

| totality | declared | result |
|---|---|---|
| succeeds | `G α` | emitted from the `TGen` witness |
| filters | `G (Option α)` | emitted by reading the carrier at `OptionT G` |
| filters | `G α` | error — declare `G (Option α)` |
| succeeds | `G (Option α)` | warning — it never fails, `G α` will do |
| *gap* | either | error / warning naming the **basis gap**, never advising `Option` |

Both emitted shapes are Basalt vocabulary throughout. `G α` is the `TGen` witness projected;
`G (Option α)` is the carrier read at `OptionT G`, so a rejecting `assume` becomes an ordinary
`pure none` draw and no `Palamedes.PGen` constant survives into the term.

The last row is a third totality outcome, distinct from "filters": reconstruction can come up empty
because the generator genuinely filters, or because the basis could not cover it. Only the first is
a fact about the generator. See `diagnoseTotality` (`Synthesizer/FrontEnd.lean`) and the section at
the bottom of this file.
-/

open Palamedes

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

/-! ## Row 2 — filtering, declared filtering: emitted at `OptionT G` -/

def genBetween (lo hi : Nat) [Gen G] : G (Option Nat) := by
  generator_search (fun n => lo ≤ n ∧ n ≤ hi)

-- Already `Option`-reflected by its type, so it samples through the retry loop directly.
#eval show IO Unit from do
  let n ← Palamedes.samplePartial (genBetween 3 7)
  unless 3 ≤ n && n ≤ 7 do
    throw <| IO.userError s!"genBetween produced {n}, outside [3,7]"

/-! ## Row 3 — filtering, declared total: an error, naming the fix

`G α` is `Fail`-free by construction, so there is no term to emit — hence an error, not a warning,
which CI would exit 0 on. -/

/--
error: generator_search: this generator filters — a `PGen.assume` survived optimization — so it cannot be emitted at
  G ℕ, which is `Fail`-free by construction.

Declare it as `G (Option _)` instead, so the type reflects that it can fail.
-/
#guard_msgs in
example (lo hi : Nat) [Gen G] : G Nat := by
  generator_search (fun n => lo ≤ n ∧ n ≤ hi)

/-! ## Row 4 — total, declared filtering: a hint, and the generator still works

The `Option` is not wrong, only unnecessary — reading the carrier at `OptionT G` works whether or
not it can fail, so there is a term to emit and, unlike row 3, this stays a warning. -/

/--
warning: this generator never fails, so the `Option` is not needed — `G (List ℕ)` will do.
-/
#guard_msgs in
def genAllTwosOpt [Gen G] : G (Option (List Nat)) := by
  generator_search (fun xs => isAllTwos xs)

/-! ## `classifyGoal` rejects goals it cannot read

The ways a goal fails to name a generator. Each is a message about the *declaration*, which is the
point: the alternative is a mismatch surfacing later from inside the emitted term, which reads as a
bug in emission rather than a fact about what was declared.
-/

-- A predicate whose domain is not the goal's element type.
/--
error: generator_search: the predicate must have type
  ℕ → Prop
-/
#guard_msgs in
example [Gen G] : G Nat := by generator_search (fun xs => isAllTwos xs)

-- A goal whose type constructor has no Basalt `Gen` instance.
/--
error: generator_search: the goal's type constructor
  List
is not a Basalt generator monad (no `Gen` instance)
-/
#guard_msgs in
example : List Nat := by generator_search (fun n => n = 2)

-- The pipeline's internal carrier is not a shape a declaration may ask for. It is rejected at the
-- universe check rather than the instance one: `PGen α` quantifies over `Gen`, so it lands in
-- `Type 1` where a Basalt generator monad is `Type → Type`.
/--
error: generator_search: the goal's type constructor
  PGen
must have type `Type → Type`, but has
  Type → Type 1
-/
#guard_msgs in
example : Palamedes.PGen Nat := by generator_search (fun n => n = 2)

-- A goal that is not an application at all, so there is no type constructor to look at.
/--
error: generator_search: the goal must be `G α` or `G (Option α)` for a Basalt `[Gen G]`, got
  ℕ
-/
#guard_msgs in
example : Nat := by generator_search (fun n => n = 2)

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

/-! ## Three renderings, two algebras

`delabDroppingSideCondition` (`PGen.lean`) is registered on three constants because Palamedes has
two generator algebras a reader can meet, not because the code is duplicated.

**Basalt's `frequency`** is what every *emitted* term chooses with, at both declared shapes: `G α` is
projected from its `TGen` witness, and `G (Option α)` is the carrier read at `OptionT G`, which
pushes through the carrier's own choices rather than leaving them.

**The carrier's `oneOf` and `frequency`** are what the *pipeline* chooses with, and are read just as
often: `set_option palamedes.debug true` prints the optimized generator, `optimize_gen` returns one,
and `PalamedesTest/Optimizer/Rewrites.lean` pins a page of them. The flatten pass produces `oneOf`;
`frequency` arises once tuning has written weights into it. Unfolding either to the Basalt
`frequency` underneath would print `{ run := fun {_G} x x_1 => frequency [(1, fun x_2 => …), …] (by
simp) }` — the `PGen.mk` wrapper, three dummy binders, and every branch eta-expanded.

All three are pinned here. Deleting any of them puts a `._proof_i` reference back into a term that
is meant to be read, and for the first, pasted. -/

section Renderings

-- Basalt's: the tactic is printed, because Basalt's autoParam is `by omega`, which cannot close the
-- goal — omitting the argument here would print a term that does not re-elaborate.
def renderBasalt [Gen G] : G Nat := frequency [(1, fun _ => pure 1), (2, fun _ => pure 2)] (by simp)

/--
info: def renderBasalt.{u_1} : {G : Type → Type u_1} → [Gen G] → G ℕ :=
fun {G} [Gen G] => frequency [(1, fun x => pure 1), (2, fun x => pure 2)]
-/
#guard_msgs in
#print renderBasalt

-- The carrier's two: the argument is dropped outright, since their autoParam is `by simp` and does
-- close it.
def renderOneOf : PGen Nat := PGen.oneOf [pure 1, pure 2]

/--
info: def renderOneOf : PGen ℕ :=
PGen.oneOf [pure 1, pure 2]
-/
#guard_msgs in
#print renderOneOf

def renderFrequency : PGen Nat := PGen.frequency [(3, pure 1), (1, pure 2)]

/--
info: def renderFrequency : PGen ℕ :=
PGen.frequency [(3, pure 1), (1, pure 2)]
-/
#guard_msgs in
#print renderFrequency

end Renderings

/-! ## A missing witness is not the same claim as "it filters"

`totality` is `repeat' first | …`, and `repeat'` does not fail — so a datatype with no `@[total]`
lemma does not throw, it simply leaves goals, exactly like a generator that genuinely filters.
Control flow alone cannot separate them, and reading the empty result as "it filters" sends the user
to add an `Option` their generator does not need. `OptionT G` accepts it, the "never fails" check is
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

private def mkResGap (gen : Lean.Expr) (gaps : Array Lean.Name) : SynthesisResult :=
  { mkRes gen none with totalityGaps := gaps }

private def diagnosisLabel : TotalityDiagnosis → String
  | .filters => "filters"
  | .gap none gaps => s!"gap (left goals, no assume){if gaps.isEmpty then "" else s!", at {gaps}"}"
  | .gap (some _) _ => "gap (errored)"

/-- info: "filters" -/
#guard_msgs in
#eval diagnosisLabel (diagnoseTotality (mkRes (Lean.mkConst ``Palamedes.PGen.assume) none))

/-- info: "gap (left goals, no assume)" -/
#guard_msgs in
#eval diagnosisLabel (diagnoseTotality (mkRes (Lean.mkConst ``Nat.zero) none))

-- ...and when the descent recorded *which* head it had no rule for, the diagnosis carries it, so
-- `gapMessage` names the missing registration rather than guessing at it.
/-- info: "gap (left goals, no assume), at #[Palamedes.PGen.mod2]" -/
#guard_msgs in
#eval diagnosisLabel (diagnoseTotality (mkResGap (Lean.mkConst ``Nat.zero) #[`Palamedes.PGen.mod2]))

-- A thrown error is a gap whatever the term contains: it is not an answer about the generator.
/-- info: "gap (errored)" -/
#guard_msgs in
#eval diagnosisLabel
  (diagnoseTotality (mkRes (Lean.mkConst ``Palamedes.PGen.assume) (some m!"boom")))
