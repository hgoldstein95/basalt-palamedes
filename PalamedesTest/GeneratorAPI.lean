import Palamedes.Synthesizer
import Palamedes.Data.List
import Palamedes.Data.Nat
import Palamedes.Sample
import Palamedes.Stats

/-!
# The generator API: one vocabulary across Basalt and Palamedes

`generator_search` dispatches on the **declared return type**, and `allow_partial` is gone: whether a
generator can fail is a fact about its type, visible at every use site.

| totality | declared | result |
|---|---|---|
| succeeds | `G α` | emitted from the `TGen` witness |
| fails | `G (Option α)` | emitted via `totalize` |
| fails | `G α` | error — declare `G (Option α)` |
| succeeds | `G (Option α)` | warning — it never fails, `G α` will do |
-/

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

/-! ## Row 1 — total, declared total: a Basalt generator, no wrapper -/

def genAllTwos [_root_.Gen G] : G (List Nat) := by
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

/-! ## Row 2 — filtering, declared filtering: the `Option` replaces `allow_partial` -/

def genBetween (lo hi : Nat) [_root_.Gen G] : G (Option Nat) := by
  generator_search (fun n => lo ≤ n ∧ n ≤ hi)

-- Already `Option`-reflected by its type, so it samples through the retry loop directly.
#eval show IO Unit from do
  let n ← Palamedes.samplePartial (genBetween 3 7)
  unless 3 ≤ n && n ≤ 7 do
    throw <| IO.userError s!"genBetween produced {n}, outside [3,7]"

/-! ## Row 3 — filtering, declared total: an error, naming the fix

`G α` is `Fail`-free by construction, so there is no term to emit. This is the one deviation from the
design note's table, which called for a warning: a warning is only implementable for the
synthesis-internal `Palamedes.Gen α` carrier, where a filtering term *does* exist. -/

/--
error: generator_search: this generator filters — a `Gen.assume` survived optimization — so it cannot be emitted at
  G ℕ, which is `Fail`-free by construction.

Declare it as `G (Option _)` instead; the `Option` is what `allow_partial` used to say.
-/
#guard_msgs in
example (lo hi : Nat) [_root_.Gen G] : G Nat := by
  generator_search (fun n => lo ≤ n ∧ n ≤ hi)

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
and `CorrectGen (P : Option β → Prop)` cannot be solved regardless of dispatch. The ambiguity the
design note worried about is therefore latent rather than live — worth keeping the escape hatch, but
it is not exercised.
-/
