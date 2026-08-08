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

`arbNat` (geometric, a direct `partial_fixpoint`), the range generators `gt`/`lt`/`mod2`, their
support and totality facts, and the range synthesis rules. The uniform range draw those rules are
built from is `PGen.choose`, which lives in `PGen.lean` beside the rest of the Basalt vocabulary;
what belongs here is everything that is about `Nat` *predicates*.
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

/-! ## The primitive

`arbNat` is the one generator here that is neither built from the core algebra nor able to fail, so
it is spelled once at the failure-free interface `TGen` and its `PGen` form is `TGen.toGen` of it,
making `total_arbNat` a direct `⟨TGen.arbNat, rfl⟩` — see `Total.lean`'s combinator section for the
criterion.

It goes in `Palamedes.TGen`, in an explicit `namespace TGen` block **outside** the `namespace PGen`
one: written inside that block it silently lands in `Palamedes.PGen.TGen`, and every file that reads
emitted terms must then `open Palamedes.PGen` to abbreviate the name — which shadows Basalt's
root-level `frequency`, so emitted generators print their choice sites as `_root_.frequency`. The
same trap is one `namespace` line away in any `Data/` module that adds a primitive. -/

namespace TGen

/-- An arbitrary natural, geometrically distributed. -/
def arbNat : TGen Nat := ⟨fun {_G} _ => arbNatGo⟩

end TGen

namespace PGen

def arbNat : PGen Nat := TGen.arbNat.toGen

@[simp]
theorem run_arbNat (G : Type → Type) [Gen G] [Fail G] : arbNat.run (G := G) = arbNatGo := rfl

/-! ### The range generators

Ordinary `PGen` composites over `arbNat` and the core `choose`: their totality witnesses come out of
the `@[total]` registry (the `Total` section below), so none needs a `TGen` spelling. `mod2` is
reached only through the filtering `s_mod2_partial`, so it needs no totality rule at all. -/

def gt (lo : Nat) : PGen Nat := (lo + 1 + · ) <$> arbNat

def mod2 (r : Nat) (_ : r < 2) : PGen Nat := (2 * · + r) <$> arbNat

def lt (hi : Nat) (_ : hi > 0) : PGen Nat :=
  choose 0 (hi - 1) (by simp)

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

@[total]
def total_arbNat : total arbNat := ⟨TGen.arbNat, rfl⟩

@[total]
def total_gt : total (gt lo) := total_map total_arbNat

@[total]
def total_lt : total (lt lo h) := total_choose

end Total

end PGen

end Palamedes
