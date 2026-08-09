/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Synthesizer
import Palamedes.Data.List

/-!
# The totality witness is extractable data

`PGen.total` is `Type`-valued, so a totality proof *is* a failure-free generator; the examples
below pin the consequences the Basalt-shaped emission stage builds on — the witness can be named,
`w.val.run` is Basalt-shaped and executable, and `w.property` transfers the support fact with no
parametricity assumption. The stages run here at the internal layer, one tactic at a time, and
isolating them is the point: the corpus exercises them only composed, where a defect in any one
shows up as a wrong emitted term rather than a failing step.
-/

open Palamedes

namespace PalamedesTest.TotalWitness

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

end PalamedesTest.TotalWitness
