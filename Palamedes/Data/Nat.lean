import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Total
import Palamedes.RuleSets
import Palamedes.CaseSplit
import Palamedes.SomeSupport

namespace Palamedes

open _root_.Palamedes.Gen

namespace Gen

/-- Polymorphic Basalt generator for an arbitrary natural number (geometrically distributed): stop at
`0`, or recurse and add one. A direct `partial_fixpoint` over Basalt's CCPO. -/
def arbNatGo [_root_.Gen G] : G Nat :=
  RandomChoice.pick
    (fun () => pure 0)
    (fun () => arbNatGo >>= fun n => pure (n + 1))
  partial_fixpoint

def arbNat : Gen Nat := ⟨fun {_G} _ _ => arbNatGo⟩

/-- Failure-free witness for `arbNat`: the same fixpoint at the `Fail`-free interface. -/
def TGen.arbNat : TGen Nat := ⟨fun {_G} _ => arbNatGo⟩

@[simp]
theorem run_arbNat (G : Type → Type) [_root_.Gen G] [Fail G] : arbNat.run (G := G) = arbNatGo := rfl

def gt (lo : Nat) : Gen Nat := (lo + 1 + · ) <$> arbNat

def mod2 (r : Nat) (_ : r < 2) : Gen Nat := (2 * · + r) <$> arbNat

def choose (lo hi : Nat) (h : lo ≤ hi := by simp) : Gen Nat :=
  ⟨fun {_G} _ _ => RandomChoice.choose lo hi h >>= fun r => Pure.pure r.down.val⟩

def TGen.choose (lo hi : Nat) (h : lo ≤ hi := by simp) : TGen Nat :=
  ⟨fun {_G} _ => RandomChoice.choose lo hi h >>= fun r => Pure.pure r.down.val⟩

def lt (hi : Nat) (_ : hi > 0) : Gen Nat :=
  choose 0 (hi - 1) (by simp)

open Lean PrettyPrinter Delaborator SubExpr in
/-- Hide `choose`'s bounds proof when both bounds are literals with `lo ≤ hi`. -/
@[app_delab Palamedes.Gen.choose]
def delabChoose : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity ``Palamedes.Gen.choose 3
  let some lo := natLit? (e.getArg! 0) | failure
  let some hi := natLit? (e.getArg! 1) | failure
  guard <| lo ≤ hi
  let loStx ← withNaryArg 0 delab
  let hiStx ← withNaryArg 1 delab
  let fn := mkIdent (← unresolveNameGlobal ``Palamedes.Gen.choose)
  `($fn $loStx $hiStx)

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
  show v ∈ SPMF.support (RandomChoice.choose lo hi h >>= fun r => Pure.pure r.down.val) ↔ _
  simp only [SPMF.support_bind, SPMF.mem_support_choose_iff, SPMF.support_pure]
  constructor
  · rintro ⟨⟨a, ha⟩, -, rfl⟩
    exact ha
  · intro hv
    exact ⟨⟨v, hv⟩, trivial, rfl⟩


@[simp] theorem someSupport_choose {lo hi : Nat} {h : lo ≤ hi} :
    someSupport (choose lo hi h) = fun a => lo ≤ a ∧ a ≤ hi := by
  funext v
  apply propext
  show some v ∈ SPMF.support (OptionT.run
      (RandomChoice.choose lo hi h >>= fun r => Pure.pure r.down.val : OptionT SPMF Nat)) ↔ _
  rw [mem_support_optionT_bind]
  simp only [instRandomChoiceOptionT, mem_support_optionT_lift, support_optionT_pure,
    SPMF.mem_support_choose_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, -, hv⟩
    cases Option.some.inj hv; exact ha
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

/-- `arbNat` is assume-free: its body uses only `pick`/`pure`/`bind`, so the same fixpoint at the
failure-free interface (`TGen.arbNat`) is a witness. (Almost-sure termination is a strictly stronger,
orthogonal fact; see the Basalt library.) -/
@[total]
def total_arbNat : total arbNat := ⟨TGen.arbNat, by ext; rfl⟩

@[total]
def total_choose : total (choose lo hi h) := ⟨TGen.choose lo hi h, by ext; rfl⟩

@[total]
def total_gt : total (gt lo) := total_map total_arbNat

@[total]
def total_lt : total (lt lo h) := total_choose

end Total

end Gen

end Palamedes
