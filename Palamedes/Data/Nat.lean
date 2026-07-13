import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Total
import Palamedes.RuleSets
import Palamedes.CaseSplit

namespace Palamedes

open Gen

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
  if h' : lo = hi then pure lo else pick (pure lo) (choose (lo + 1) hi (by omega))

def lt (hi : Nat) (_ : hi > 0) : Gen Nat :=
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

@[simp]
theorem support_choose :
    support (choose lo hi h) = fun a => lo ≤ a ∧ a ≤ hi := by
  generalize hn : hi - lo = n
  funext v
  induction n generalizing lo hi v with
  | zero =>
    unfold choose
    split <;> simp <;> omega
  | succ n' ih =>
    unfold choose
    split
    . simp
      omega
    . simp
      apply Iff.intro
      . intro hv
        cases hv with
        | inl hv => simp_all
        | inr hv =>
          have h : hi - (lo + 1) = n' := by omega
          rw [ih h] at hv
          omega
      . intro hbw
        by_cases v = lo
        . left; assumption
        . right
          rw [ih _] <;> omega

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
@[simp, aesop safe (rule_sets := [totality])]
theorem total_arbNat : total arbNat := ⟨TGen.arbNat, by ext; rfl⟩

@[simp, aesop safe (rule_sets := [totality])]
theorem total_choose : total (choose lo hi h) := by
  generalize hn : hi - lo = n
  induction n generalizing lo hi h with
  | zero =>
    unfold choose
    have : lo = hi := by omega
    simp [this]
  | succ n' ih =>
    unfold choose
    split
    . simp
    . apply total_pick
      . simp
      . apply ih
        omega

@[simp, aesop safe (rule_sets := [totality])]
theorem total_gt : total (gt lo) := by simp [gt]

@[simp, aesop safe (rule_sets := [totality])]
theorem total_lt : total (lt lo h) := by simp [lt]

end Total

end Gen

end Palamedes
