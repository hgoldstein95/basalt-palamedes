/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Synthesizer
import Palamedes.Data.List

/-!
# The totality witness is extractable data

`PGen.total` is `Type`-valued, so a totality proof *is* a failure-free generator. This file pins the
three consequences that the Basalt-shaped emission stage builds on:

1. the witness can be **named** — it survives out of the `totality` tactic as an ordinary value;
2. `w.val.run` is **Basalt-shaped** (`∀ {G} [Gen G], G α`, no `Fail`) and **executable**, so Basalt's
   own tooling accepts it directly;
3. `w.property` **transfers the support fact** from the Palamedes generator to the emitted one,
   without any parametricity assumption — both sides are the *same* instantiation, at `SPMF`.

(3) is why the total path's law is Basalt's `IsSoundAndComplete` where the filtering path's is
`IsSomeSoundAndComplete`: a filtering generator is read at `OptionT SPMF`, a *different*
instantiation, so the transfer does not go through and the law is stated at that interpretation's
own support notion instead.

The three steps are spelled out here **at the internal layer**, one tactic at a time. That is not
how a generator is declared — `generator_search` takes a Basalt goal and runs the whole pipeline, so
the `PGen` below never surfaces — and isolating them is the point: the corpus exercises the steps
only composed, where a defect in any one shows up as a wrong emitted term rather than a failing step.
-/

open Palamedes

@[simp]
def isAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && isAllTwos xs

-- Stages 1–3 by hand: search for a `CorrectGen`, then extract and optimize the `PGen` inside it.
def genAllTwos : Palamedes.PGen (List Nat) := by
  optimize_gen (show CorrectGen (fun xs => isAllTwos xs = true) by cgenerator_search).val

-- 1. The witness is data, so it can be given a name and a type.
def genAllTwosWitness : PGen.total genAllTwos := by totality

-- 2. It is Basalt-shaped: polymorphic in `G` over Basalt's own `Gen` class, with no `Fail`.
def genAllTwosBasalt [Gen G] : G (List Nat) := genAllTwosWitness.val.run

-- 3. The support fact crosses to the emitted generator definitionally.
example : SPMF.support (genAllTwosBasalt (G := SPMF)) = genAllTwos.support := by
  conv_rhs => rw [← genAllTwosWitness.property]
  rfl

-- The computability check that matters: Basalt's own tooling consumes the synthesized generator
-- with no adapter, and to print this it had to actually *run* it — so the witness carries code,
-- not `Classical.choice`.
/--
info: genAllTwosBasalt — 50 draws (seed 0, fuel 10000)

  outcomes    ok 50 (100.0%)
  size        mean 1.8   p50 1   p95 4   max 5
  choices     mean 1.8   p50 1   p95 4   max 5
  distinct    5 / 50

  head constructor
    nil     56.0%  (28)
    cons    44.0%  (22)

  most common
     56.0%  (28)  []
     18.0%   (9)  [2]
     14.0%   (7)  [2, 2]
     10.0%   (5)  [2, 2, 2]

  samples
    [2, 2]
    []
    []
-/
#guard_msgs in
#genstats (draws := 50) genAllTwosBasalt
