/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.PGen
import Palamedes.CorrectGen
import Palamedes.Total
import Palamedes.RuleSets
import Palamedes.CaseSplit
import Palamedes.SomeSupport

/-!
# `Nat` primitives

`arbNat` (geometric, a direct `partial_fixpoint`), the range generators `choose`/`gt`/`lt`/`mod2`,
their support and totality facts, and the range synthesis rules (`s_between`,
`s_between_partial`, `s_gt`, `s_lt_partial`, `s_mod2_partial`). Also `delabChoose`, which keeps
`generator_search?` output for `choose` re-elaborable without printing its side-condition proof.
-/

namespace Palamedes

open Palamedes.PGen

namespace PGen

/-- Polymorphic Basalt generator for an arbitrary natural number (geometrically distributed): stop at
`0`, or recurse and add one. A direct `partial_fixpoint` over Basalt's CCPO. -/
def arbNatGo [Gen G] : G Nat :=
  RandomChoice.pick
    (fun () => pure 0)
    (fun () => arbNatGo >>= fun n => pure (n + 1))
  partial_fixpoint

end PGen

/-! ## The primitives

`arbNat` and `choose` are the two generators here that are neither built from the core algebra nor
able to fail, so each is spelled once at the failure-free interface `TGen` and its `PGen` form is
`TGen.toGen` of it. That direction makes `total_arbNat`/`total_choose` direct `⟨witness, rfl⟩` pairs:
the witness a totality proof has to produce is the definition itself, rather than a separately
written mirror of it that a lemma then has to reconnect.

Deliberately `Palamedes.TGen`, beside the type and the core algebra (`TGen.pure`, `TGen.bind`,
`TGen.frequency`, … in `Total.lean`) — **not** `Palamedes.PGen.TGen`, which is where these two would
land if written inside a `namespace PGen` block. Two namespaces both *printing* as `TGen` is
confusing on its own, and the cost is concrete: it forces every file that reads emitted terms to
`open Palamedes.PGen` in order to abbreviate `PGen.TGen.choose`, and that open shadows Basalt's
root-level `frequency`, so the generator Palamedes emits prints as `_root_.frequency`. The same trap
is one `namespace` line away in any `Data/` module that adds a primitive. -/

namespace TGen

/-- An arbitrary natural, geometrically distributed. -/
def arbNat : TGen Nat := ⟨fun {_G} _ => arbNatGo⟩

/-- A uniform draw from `[lo, hi]`, and what a Basalt-shaped generator emits for a range; see
`delabTGenChoose`.

The draw itself is Basalt's `chooseNat`, not a re-spelling of it: `TGen Nat` is exactly the type of a
`Gen`-polymorphic `G Nat`, so viewing a Basalt primitive as failure-free costs a `TGen.mk` and
nothing else. Re-spelling it would additionally owe an argument that the two agree, and `chooseNat`'s
support and mass lemmas would not apply. -/
def choose (lo hi : Nat) (h : lo ≤ hi := by gen_side_condition) : TGen Nat :=
  ⟨fun {_G} _ => chooseNat lo hi h⟩

end TGen

namespace PGen

def arbNat : PGen Nat := TGen.arbNat.toGen

@[simp]
theorem run_arbNat (G : Type → Type) [Gen G] [Fail G] : arbNat.run (G := G) = arbNatGo := rfl

def choose (lo hi : Nat) (h : lo ≤ hi := by gen_side_condition) : PGen Nat :=
  (TGen.choose lo hi h).toGen

/-! ### Composites over them

The three below are ordinary `PGen` definitions, and the `TGen`-first direction above is not meant to
reach them. It earns its keep only where a totality witness has to be written by hand, since that is
what a `PGen`-side primitive costs a second body for. These compose, so their witnesses come out of
the `@[total]` registry — `total_gt` is `total_map total_arbNat` and `total_lt` is `total_choose` —
and there is no second body either way. (`mod2` is reached only through the filtering
`s_mod2_partial`, so it needs no totality rule at all.) -/

def gt (lo : Nat) : PGen Nat := (lo + 1 + · ) <$> arbNat

def mod2 (r : Nat) (_ : r < 2) : PGen Nat := (2 * · + r) <$> arbNat

def lt (hi : Nat) (_ : hi > 0) : PGen Nat :=
  choose 0 (hi - 1) (by simp)

open Lean PrettyPrinter Delaborator SubExpr in

/-- Print `choose lo hi` without its side-condition proof, so `generator_search?` output
re-elaborates (the `by gen_side_condition` autoParam recovers it). Fires only when the proof is
recoverable: literal bounds, or an auxiliary `._proof_i` closed over local hypotheses, which is
exactly the shape that would otherwise print as an unpasteable reference. -/
def delabChooseFor (c : Name) : Delab :=
  delabDroppingProof c 3 [0, 1] fun e =>
    let litBounds : Bool := Id.run do
      let some lo := natLit? (e.getArg! 0) | return false
      let some hi := natLit? (e.getArg! 1) | return false
      return lo ≤ hi
    litBounds || isAuxProofOverLocals (e.getArg! 2)

open Lean PrettyPrinter Delaborator in

@[app_delab Palamedes.PGen.choose]
def delabChoose : Delab := delabChooseFor ``Palamedes.PGen.choose

open Lean PrettyPrinter Delaborator in

/-- The same for the failure-free twin, which is what a **Basalt-shaped** generator emits: the
totality witness is built from `TGen.choose`, and `extractWitness` deliberately stops short of
unfolding it. Without this registration `genBST` at `[Gen G] : G _` prints
`(TGen.choose lo hi (s_between_partial._proof_1 hb)).run` — a `._proof_1` reference in a term whose
whole purpose is to be read and pasted. Exactly the reason `delabDroppingSideCondition` is
registered on three constants rather than one; see `PGen.lean`. -/
@[app_delab Palamedes.TGen.choose]
def delabTGenChoose : Delab := delabChooseFor ``Palamedes.TGen.choose

@[simp]
theorem support_arbNat :
    support arbNat = fun _ => True := by
  funext v
  apply propext
  simp only [iff_true]
  show v ∈ SPMF.support arbNatGo
  induction v with
  | zero => rw [arbNatGo]; simp
  | succ n ih => rw [arbNatGo]; simp_all


@[simp] theorem someSupport_arbNat : someSupport arbNat = fun _ => True := by
  funext v
  apply propext
  simp only [iff_true]
  show some v ∈ SPMF.support (OptionT.run (arbNatGo (G := OptionT SPMF)))
  induction v with
  | zero =>
    rw [arbNatGo, mem_support_optionT_pick]
    exact Or.inl (by rw [support_optionT_pure]; simp)
  | succ n ih =>
    rw [arbNatGo, mem_support_optionT_pick]
    refine Or.inr ?_
    rw [mem_support_optionT_bind]
    exact ⟨n, ih, by rw [support_optionT_pure]; simp⟩
@[simp]
theorem support_gt :
    support (gt lo) = fun a => lo < a := by
  simp [gt]
  funext a
  simp
  apply Iff.intro
  . omega
  . intro h
    induction h with
    | refl => simp
    | step a ih =>
      have ⟨x, hx⟩ := ih
      exists x + 1
      omega


@[simp] theorem someSupport_gt {lo : Nat} : someSupport (gt lo) = fun a => lo < a := by
  simp only [gt, someSupport_map, someSupport_arbNat]
  funext a; apply propext; constructor
  · rintro ⟨x, -, rfl⟩; omega
  · intro h; exact ⟨a - lo - 1, trivial, by omega⟩
@[simp]
theorem support_mod2 :
    support (mod2 r h) = fun a => a % 2 = r := by
  simp [mod2]
  funext a
  simp
  apply Iff.intro
  . omega
  . intro h1
    exists (a/2)
    rw [←h1, Nat.div_add_mod]


@[simp] theorem someSupport_mod2 {r : Nat} {h : r < 2} :
    someSupport (mod2 r h) = fun a => a % 2 = r := by
  simp only [mod2, someSupport_map, someSupport_arbNat]
  funext a; apply propext; constructor
  · rintro ⟨x, -, rfl⟩; omega
  · intro h1; exact ⟨a / 2, trivial, by rw [← h1, Nat.div_add_mod]⟩
@[simp]
theorem support_choose :
    support (choose lo hi h) = fun a => lo ≤ a ∧ a ≤ hi := by
  funext v
  apply propext
  show v ∈ SPMF.support (chooseNat lo hi h) ↔ _
  exact SPMF.mem_support_chooseNat_iff


@[simp] theorem someSupport_choose {lo hi : Nat} {h : lo ≤ hi} :
    someSupport (choose lo hi h) = fun a => lo ≤ a ∧ a ≤ hi := by
  funext v
  apply propext
  show some v ∈ SPMF.support (OptionT.run (chooseNat lo hi h : OptionT SPMF Nat)) ↔ _
  rw [show (chooseNat lo hi h : OptionT SPMF Nat)
      = (·.down.val) <$> RandomChoice.choose lo hi h from rfl, mem_support_optionT_map]
  simp only [instRandomChoiceOptionT, mem_support_optionT_lift, SPMF.mem_support_choose_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, -, rfl⟩
    exact ha
  · intro hv
    exact ⟨⟨v, hv⟩, trivial, rfl⟩
@[simp]
theorem support_lt :
    support (lt hi h) = fun a => a < hi := by
  simp [lt]
  funext a
  simp
  apply Iff.intro
  . intro
    omega
  . intro
    omega


@[simp] theorem someSupport_lt {hi : Nat} {h : hi > 0} :
    someSupport (lt hi h) = fun a => a < hi := by
  simp only [lt, someSupport_choose]
  funext a; apply propext; constructor
  · rintro ⟨-, h2⟩; omega
  · intro h2; omega
namespace CorrectGen

@[extract, aesop safe apply (rule_sets := [synthesis])]
def s_arbNat : @CorrectGen Nat (fun _ => True) :=
  Subtype.mk arbNat <| by
    funext v
    simp

@[extract, case_split]
def s_caseNat
    {Q : α → Prop}
    {P : α → Nat → Prop}
    (n : Nat)
    (h : ∀ {a}, P a n = Q a)
    (gz : CorrectGen (fun a => P a 0))
    (gs : (n' : Nat) → CorrectGen (fun a => P a (n' + 1))) :
    CorrectGen Q :=
  Subtype.mk (if n = 0 then gz.val else (gs n.pred).val) <| by
    match n with
    | 0 => simp [gz.property, h]
    | n' + 1 => simp [(gs n').property, h]

@[extract]
def s_between
    {lo hi : Nat}
    (h : lo ≤ hi) :
    CorrectGen (fun v => lo ≤ v ∧ v ≤ hi) :=
  Subtype.mk (choose lo hi h) <| by
    funext v
    simp

@[extract]
def s_between_partial
    {lo hi : Nat} :
    CorrectGen (fun v => lo ≤ v ∧ v ≤ hi) :=
  Subtype.mk (assume (lo ≤ hi) (fun h => choose lo hi (by simp_all only [decide_eq_true_eq]))) <| by
    funext v
    simp
    exact Nat.le_trans

@[extract]
def s_gt
    {lo : Nat} :
    CorrectGen (fun v => lo < v) :=
  Subtype.mk (gt lo) <| by
    simp

@[extract]
def s_lt_partial
    {hi : Nat} :
    CorrectGen (λ v => v < hi) :=
  Subtype.mk (assume (hi > 0) (fun h => lt hi (by aesop))) <| by
    simp
    funext
    simp
    exact fun a => Nat.zero_lt_of_lt a

@[extract]
def s_mod2_partial
    {r : Nat} :
    CorrectGen (λ v => v % 2 = r) :=
  Subtype.mk (assume (r < 2) (fun h => mod2 r (by aesop))) <| by
    simp
    funext x
    simp
    omega

end CorrectGen

namespace Total

/-- `arbNat` is assume-free by construction: it *is* `TGen.arbNat` viewed as a `PGen`, so the witness
is that generator and the equation is `rfl`. (Almost-sure termination is a strictly stronger,
orthogonal fact; see the Basalt library.) -/
@[total]
def total_arbNat : total arbNat := ⟨TGen.arbNat, rfl⟩

@[total]
def total_choose : total (choose lo hi h) := ⟨TGen.choose lo hi h, rfl⟩

@[total]
def total_gt : total (gt lo) := total_map total_arbNat

@[total]
def total_lt : total (lt lo h) := total_choose

end Total

end PGen

end Palamedes
