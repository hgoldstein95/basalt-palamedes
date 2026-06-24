import Palamedes.Gen
import Palamedes.OptimizeCongr
import Palamedes.CorrectGen
import Palamedes.Total
import Palamedes.Data.STLC.Ty
import Palamedes.Util

section TypeDef

inductive Term : Type where
  | unit
  | var (n : Nat)
  | abs (τ : Ty) (t : Term)
  | app (t₁ t₂ : Term)
  deriving Repr

end TypeDef

section BaseFunctor

inductive TermF (α : Type) where
  | unit : TermF α
  | var : (n : Nat) → TermF α
  | abs : (τ : Ty) → (t : α) → TermF α
  | app : (t₁ t₂ : α) → TermF α

theorem TermF_or
    {α : Type}
    {P : Prop}
    {Q : Nat → Prop}
    {R : Ty → α → Prop}
    {S : α → α → Prop}
    {t : TermF α} :
    TermF.rec P Q R S t ↔
    (t = .unit ∧ P) ∨
      (∃ n, t = .var n ∧ Q n) ∨
      (∃ τ x, t = .abs τ x ∧ R τ x) ∨
      (∃ x₁ x₂, t = .app x₁ x₂ ∧ S x₁ x₂) := by
    cases t <;> aesop

end BaseFunctor

section RecursionSchemes

def Term.fold
    {α : Type}
    (z : α)
    (zn : Nat → α)
    (f_abs : Ty → α → α)
    (f_app: α → α → α)
    (t : Term) :
    α :=
  match t with
  | .unit => z
  | .var n => zn n
  | .abs τ t' => f_abs τ (Term.fold z zn f_abs f_app t')
  | .app t₁ t₂ =>
    f_app (Term.fold z zn f_abs f_app t₁) (Term.fold z zn f_abs f_app t₂)

@[simp] theorem Term.fold_unit :
  Term.fold z zn f_abs f_app .unit = z := rfl
@[simp] theorem Term.fold_var {n : Nat} :
  Term.fold z zn f_abs f_app (.var n) = zn n := rfl
@[simp] theorem Term.fold_abs {τ : Ty} {t : Term} :
  Term.fold z zn f_abs f_app (.abs τ t) =
    f_abs τ (Term.fold z zn f_abs f_app t) := rfl
@[simp] theorem Term.fold_app {t₁ t₂ : Term} :
  Term.fold z zn f_abs f_app (.app t₁ t₂) =
    f_app (Term.fold z zn f_abs f_app t₁) (Term.fold z zn f_abs f_app t₂)
    := rfl

def Term.accuM
    [Monad m]
    {α σ : Type}
    (st_abs : Ty → σ → σ)
    (st_app : σ → σ × σ)
    (z : σ → m α)
    (zn : Nat → σ → m α)
    (f_abs : Ty → α → σ → m α)
    (f_app : α → α → σ → m α)
    (t : Term)
    (i : σ) :
    m α :=
  match t with
  | .unit => z i
  | .var n => zn n i
  | .abs τ t' => do
    let v' ← Term.accuM st_abs st_app z zn f_abs f_app t' (st_abs τ i)
    f_abs τ v' i
  | .app t₁ t₂ => do
    let (s₁, s₂) := st_app i
    let v₁ ← Term.accuM st_abs st_app z zn f_abs f_app t₁ s₁
    let v₂ ← Term.accuM st_abs st_app z zn f_abs f_app t₂ s₂
    f_app v₁ v₂ i

@[simp] theorem Term.accuM_unit [Monad m] {st_abs : Ty → σ → σ}
  {st_app : σ → σ × σ} {z : σ → m α} {zn : Nat → σ → m α}
  {f_abs : Ty → α → σ → m α} {f_app : α → α → σ → m α} {i : σ} :
  Term.accuM st_abs st_app z zn f_abs f_app (.unit : Term) i = z i := rfl
@[simp] theorem Term.accuM_var [Monad m] {st_abs : Ty → σ → σ}
  {st_app : σ → σ × σ} {z : σ → m α} {zn : Nat → σ → m α}
  {f_abs : Ty → α → σ → m α} {f_app : α → α → σ → m α} {i : σ} {n : Nat} :
  Term.accuM st_abs st_app z zn f_abs f_app (.var n : Term) i = zn n i := rfl
@[simp] theorem Term.accuM_abs [Monad m]  {st_abs : Ty → σ → σ}
  {st_app : σ → σ × σ} {z : σ → m α} {zn : Nat → σ → m α}
  {f_abs : Ty → α → σ → m α} {f_app : α → α → σ → m α} {i : σ}
  {τ : Ty} {t : Term} :
  Term.accuM st_abs st_app z zn f_abs f_app (.abs τ t : Term) i = (do
    let v' ← Term.accuM st_abs st_app z zn f_abs f_app t (st_abs τ i)
    f_abs τ v' i) := rfl
@[simp] theorem Term.accuM_app [Monad m] {st_abs : Ty → σ → σ}
  {st_app : σ → σ × σ} {z : σ → m α} {zn : Nat → σ → m α}
  {f_abs : Ty → α → σ → m α} {f_app : α → α → σ → m α} {i : σ} {t₁ t₂ : Term} :
  Term.accuM st_abs st_app z zn f_abs f_app (.app t₁ t₂ : Term) i = (do
    let (s₁, s₂) := st_app i
    let v₁ ← Term.accuM st_abs st_app z zn f_abs f_app t₁ s₁
    let v₂ ← Term.accuM st_abs st_app z zn f_abs f_app t₂ s₂
    f_app v₁ v₂ i) := rfl

end RecursionSchemes

section Unfold

namespace Palamedes

open Gen

/-- The polymorphic Basalt generator underlying the term `unfold`: `unit`/`var` stop, `abs` recurses
on its body, `app` recurses on both subterms. A direct `partial_fixpoint` over Basalt's CCPO. -/
def Term.unfoldGo [_root_.Gen G] (step : α → G (TermF α)) (x : α) : G Term :=
  step x >>= fun t =>
    match t with
    | .unit => pure .unit
    | .var n => pure (.var n)
    | .abs τ x' => Term.unfoldGo step x' >>= fun t' => pure (.abs τ t')
    | .app x₁ x₂ =>
      Term.unfoldGo step x₁ >>= fun t₁ =>
      Term.unfoldGo step x₂ >>= fun t₂ =>
      pure (.app t₁ t₂)
  partial_fixpoint

def Term.unfold (f : α → Gen (TermF α)) (x : α) : Gen Term :=
  ⟨fun {_G} _ _ => Term.unfoldGo (fun b => (f b).run) x⟩

/-- Failure-free witness for `Term.unfold`: the same fixpoint at the `Fail`-free interface. -/
def TGen.Term.unfold (f : α → TGen (TermF α)) (x : α) : TGen Term :=
  ⟨fun {_G} _ => Palamedes.Term.unfoldGo (fun b => (f b).run) x⟩

@[simp]
theorem Term.run_unfold (f : α → Gen (TermF α)) (x : α) (G : Type → Type) [_root_.Gen G] [Fail G] :
    (Term.unfold f x).run (G := G) = Term.unfoldGo (fun b => (f b).run) x := rfl

@[simp]
def Term.unfold_support (P : α → TermF α → Prop) (x : α) (t : Term) : Prop :=
  match t with
  | .unit => P x .unit
  | .var n => P x (.var n)
  | .abs τ t' => ∃ x',
    P x (.abs τ x') ∧
    Term.unfold_support P x' t'
  | .app t₁ t₂ => ∃ x₁ x₂,
    P x (.app x₁ x₂) ∧
    Term.unfold_support P x₁ t₁ ∧
    Term.unfold_support P x₂ t₂

@[simp]
theorem Term.support_unfold :
    support (Term.unfold f x) = Term.unfold_support (fun x' => support (f x')) x := by
  funext t
  apply propext
  show t ∈ SPMF.support (Term.unfoldGo (fun b => (f b).run) x) ↔
    Term.unfold_support (fun x' => support (f x')) x t
  induction t generalizing x with
  | unit =>
    unfold Term.unfoldGo
    rw [SPMF.support_bind]
    simp only [Set.mem_setOf_eq, Term.unfold_support]
    constructor
    · rintro ⟨t, ht, hxs⟩
      cases t with
      | unit => exact ht
      | var n => simp at hxs
      | abs τ x' => simp at hxs
      | app x₁ x₂ => simp at hxs
    · intro h
      exact ⟨.unit, h, by simp⟩
  | var m =>
    unfold Term.unfoldGo
    rw [SPMF.support_bind]
    simp only [Set.mem_setOf_eq, Term.unfold_support]
    constructor
    · rintro ⟨t, ht, hxs⟩
      cases t with
      | unit => simp at hxs
      | var n =>
        simp only [SPMF.support_pure, Set.mem_singleton_iff] at hxs
        obtain rfl := Term.var.inj hxs.symm
        exact ht
      | abs τ x' => simp at hxs
      | app x₁ x₂ => simp at hxs
    · intro h
      exact ⟨.var m, h, by simp⟩
  | abs τ t' ih =>
    unfold Term.unfoldGo
    rw [SPMF.support_bind]
    simp only [Set.mem_setOf_eq, Term.unfold_support]
    constructor
    · rintro ⟨t, ht, hxs⟩
      cases t with
      | unit => simp at hxs
      | var n => simp at hxs
      | abs τ' x' =>
        simp only [SPMF.support_bind, SPMF.support_pure, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at hxs
        obtain ⟨s', hs', heq⟩ := hxs
        obtain ⟨rfl, rfl⟩ := Term.abs.inj heq.symm
        exact ⟨x', ht, ih.mp hs'⟩
      | app x₁ x₂ => simp at hxs
    · rintro ⟨x', hx', hs⟩
      refine ⟨.abs τ x', hx', ?_⟩
      simp only [SPMF.support_bind, SPMF.support_pure, Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨t', ih.mpr hs, rfl⟩
  | app t₁ t₂ ih₁ ih₂ =>
    unfold Term.unfoldGo
    rw [SPMF.support_bind]
    simp only [Set.mem_setOf_eq, Term.unfold_support]
    constructor
    · rintro ⟨t, ht, hxs⟩
      cases t with
      | unit => simp at hxs
      | var n => simp at hxs
      | abs τ' x' => simp at hxs
      | app x₁ x₂ =>
        simp only [SPMF.support_bind, SPMF.support_pure, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at hxs
        obtain ⟨s₁, hs₁, s₂, hs₂, heq⟩ := hxs
        obtain ⟨rfl, rfl⟩ := Term.app.inj heq.symm
        exact ⟨x₁, x₂, ht, ih₁.mp hs₁, ih₂.mp hs₂⟩
    · rintro ⟨x₁, x₂, hx, h₁, h₂⟩
      refine ⟨.app x₁ x₂, hx, ?_⟩
      simp only [SPMF.support_bind, SPMF.support_pure, Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨t₁, ih₁.mpr h₁, t₂, ih₂.mpr h₂, rfl⟩

@[gen_congr]
theorem Term.support_unfold_congr
    {hf : ∀ {b}, support (f b) = support (f' b)} :
    support (Term.unfold f b) = support (Term.unfold f' b) := by
  aesop

end Palamedes

end Unfold

section FoldConversions

theorem Term.fold_accu_Option_basic
    {α : Type}
    {v : α}
    {t : Term}
    (z : α)
    (zn : Nat → α)
    (f_abs : Ty → α → α)
    (f_app: α → α → α) :
    Term.fold z zn f_abs f_app t = v ↔
    Term.accuM
      (fun _ _ => ())
      (fun _ => ((), ()))
      (fun _ => some z)
      (fun n _ => some (zn n))
      (fun τ t' _ => some (f_abs τ t'))
      (fun t₁ t₂ _ => some (f_app t₁ t₂))
      t
      () = some v := by
    induction t generalizing v <;> simp_all [Term.fold, Term.accuM]
    case abs τ t' ih =>
      replace ih := @ih (Term.fold z zn f_abs f_app t')
      simp_all
    case app t₁ t₂ ih₁ ih₂ =>
      replace ih₁ := @ih₁ (Term.fold z zn f_abs f_app t₁)
      replace ih₂ := @ih₂ (Term.fold z zn f_abs f_app t₂)
      simp_all

theorem Term.fold_accu_Option_true
    {t : Term}
    {f_var : Nat → Bool}
    {f_abs : Ty → Bool → Bool}
    {f_app : Bool → Bool → Bool}
    {g_abs : Ty → Bool}
    (h_abs : ∀ τ acc, f_abs τ acc = (g_abs τ && acc))
    (h_app : ∀ acc₁ acc₂, f_app acc₁ acc₂ = (acc₁ && acc₂)) :
    Term.fold true f_var f_abs f_app t = true ↔
    Term.accuM
      (fun _ _ => ())
      (fun _ => ((), ()))
      (fun _ => some ())
      (fun n _  => guard (f_var n))
      (fun τ _ _ => guard (g_abs τ))
      (fun _ _ _ => some ())
      t
      () = some () := by
    induction t <;> simp_all [Term.fold, Term.accuM, guard]
    case abs τ t' ih =>
      apply Iff.intro <;> intro hf
      . -- (->)
        generalize hv' : fold true f_var f_abs f_app t' = v'
        cases v' <;>
          simp_all
      . -- (<-)
        rw [Option.bind_eq_some_iff] at hf
        replace ⟨ v₁, hf ⟩ := hf
        simp_all
    case app t₁ t₂ ih₁ ih₂ =>
      apply Iff.intro <;> intro hf
      . -- (->)
        generalize hv₁ : fold true f_var f_abs f_app  t₁ = v₁
        generalize hv₂ : fold true f_var f_abs f_app  t₂ = v₂
        cases v₁ <;> cases v₂ <;>
          simp_all
      . -- (<-)
        rw [Option.bind_eq_some_iff] at hf
        replace ⟨ v₁, hf ⟩ := hf
        rw [Option.bind_eq_some_iff] at hf
        replace ⟨ h₁, ⟨ v₂, h₂ ⟩ ⟩ := hf
        simp_all

theorem Term.fold_accu_Option_function
    {α σ : Type}
    {i : σ}
    {v : α}
    {t : Term}
    {z : (σ → α)}
    {zn : Nat → (σ → α)}
    {f_abs : Ty → (σ → α) → (σ → α)}
    {f_app : (σ → α) → (σ → α) → (σ → α)}
    {g_abs : Ty → α → σ → Option α}
    {g_app : α → α → σ → Option α}
    {st_abs : Ty → σ → σ}
    {st_app₁ st_app₂ : σ → σ}
    (h_abs : ∀ τ acc s w,
      f_abs τ acc s = w ↔ (do g_abs τ (← acc (st_abs τ s)) s) = some w)
    (h_app : ∀ acc₁ acc₂ s w,
      f_app acc₁ acc₂ s = w ↔
        (do g_app (← acc₁ (st_app₁ s)) (← acc₂ (st_app₂ s)) s) = some w)
    :
    Term.fold z zn f_abs f_app t i = v ↔
    Term.accuM
      st_abs
      (fun s => (st_app₁ s, st_app₂ s))
      (fun s => some (z s))
      (fun n s => some (zn n s))
      g_abs
      g_app
      t
      i = some v := by
    induction t generalizing v i <;> simp_all [Term.fold, Term.accuM, Option.bind_eq_some_iff]
    case abs τ t' ih =>
      apply Iff.intro <;> intro hg
      . -- (->)
        exists Term.fold z zn f_abs f_app t' (st_abs τ i)
        rw [← ih]
        simp_all
      . -- (<-)
        replace ⟨ v', h', hg ⟩ := hg
        rw [← ih] at h'
        rw [h']
        apply hg
    case app t₁ t₂ ih₁ ih₂ =>
      apply Iff.intro <;> intro hg
      . -- (->)
        exists Term.fold z zn f_abs f_app t₁ (st_app₁ i)
        rw [← ih₁]; simp_all
        exists Term.fold z zn f_abs f_app t₂ (st_app₂ i)
        rw [← ih₂]; simp_all
      . -- (<-)
        replace ⟨ v₁, h₁, v₂, h₂, hg ⟩ := hg
        rw [← ih₁] at h₁
        rw [← ih₂] at h₂
        rw [h₁, h₂]
        apply hg

theorem Term.fold_accu_Option_function_true
    {σ : Type}
    {i : σ}
    {t : Term}
    {f_var : Nat → (σ → Bool)}
    {f_abs : Ty → (σ → Bool) → (σ → Bool)}
    {f_app : (σ → Bool) → (σ → Bool) → (σ → Bool)}
    {g_abs : Ty → (σ → Bool)}
    {st_abs : Ty → σ → σ}
    {st_app₁ st_app₂ : σ → σ}
    (h_abs : ∀ τ acc s,
      f_abs τ acc s = true ↔
      (do (return (g_abs τ s) && (← acc (st_abs τ s)))) = some true)
    (h_app : ∀ acc₁ acc₂ s,
      f_app acc₁ acc₂ s = true ↔
      (do (return (← acc₁ (st_app₁ s)) && (← acc₂ (st_app₂ s)))) = some true)
    :
    Term.fold (fun _ => true) f_var f_abs f_app t i = true ↔
    Term.accuM
      st_abs
      (fun s => (st_app₁ s, st_app₂ s))
      (fun _ => some ())
      (fun n s => guard (f_var n s))
      (fun τ _ s => guard (g_abs τ s))
      (fun _ _ _ => some ())
      t
      i = some () := by
    induction t generalizing i <;> simp_all [Term.fold, Term.accuM, Option.bind_eq_some_iff, guard]
    case abs τ t' ih =>
      apply Iff.intro <;> intro hg <;> simp_all
      replace ⟨⟨ v', h' ⟩ , hg⟩ := hg; simp_all
    case app t₁ t₂ ih₁ ih₂ =>
      apply Iff.intro <;> intro hg <;> try simp_all
      replace ⟨ ⟨ v₁, h₁ ⟩ , ⟨ v₂, h₂ ⟩  ⟩ := hg; clear hg; simp_all

theorem Term.fold_accu_Option_function_Option
    {α σ : Type}
    {i : σ}
    {v : α}
    {t : Term}
    {z : (σ → Option α)}
    {zn : Nat → (σ → Option α)}
    {f_abs : Ty → (σ → Option α) → (σ → Option α)}
    {f_app : (σ → Option α) → (σ → Option α) → (σ → Option α)}
    {g_abs : Ty → α → σ → Option α}
    {g_app : α → α → σ → Option α}
    {st_abs : Ty → σ → σ}
    {st_app₁ st_app₂ : σ → σ}
    (h_abs : ∀ τ acc s w,
      f_abs τ acc s = some w ↔ (do g_abs τ (← acc (st_abs τ s)) s) = some w)
    (h_app : ∀ acc₁ acc₂ s w,
      f_app acc₁ acc₂ s = some w ↔
        (do g_app (← acc₁ (st_app₁ s)) (← acc₂ (st_app₂ s)) s) = some w)
    :
    Term.fold z zn f_abs f_app t i = some v ↔
    Term.accuM
      st_abs
      (fun s => (st_app₁ s, st_app₂ s))
      (fun s => z s)
      (fun n s => zn n s)
      g_abs
      g_app
      t
      i = some v := by
  induction t generalizing i v <;> simp_all [Term.fold, Term.accuM, Option.bind_eq_some_iff]

end FoldConversions

section FoldCoercion

theorem Term.coerce_to_fold
    {t : Term}
    {f : Term → α} -- function to be coerced
    {z : α}
    {zn : Nat → α}
    {g_abs : Ty → α → α}
    {g_app : α → α → α}
    (h_unit : f .unit = z := by rflm)
    (h_var : ∀ n, f (.var n) = zn n := by rflm)
    (h_abs : ∀ τ t', f (.abs τ t') = g_abs τ (f t') := by intros; simp_all; rflm)
    (h_app : ∀ t₁ t₂, f (.app t₁ t₂) = g_app (f t₁) (f t₂) := by intros; simp_all; rflm) :
    f t = t.fold z zn g_abs g_app := by
  induction t <;> simp_all

end FoldCoercion

section FoldMerging

theorem Term.merge_accu_Option
    {t : Term}
    {st_abs₁ : Ty → σ₁ → σ₁} {st_abs₂ : Ty → σ₂ → σ₂}
    {st_app₁ : σ₁ → σ₁ × σ₁} {st_app₂ : σ₂ → σ₂ × σ₂}
    {z₁ : σ₁ → Option α₁} {z₂ : σ₂ → Option α₂}
    {zn₁ : Nat → σ₁ → Option α₁} {zn₂ : Nat → σ₂ → Option α₂}
    {f_abs₁ : Ty → α₁ → σ₁ → Option α₁} {f_abs₂ : Ty → α₂ → σ₂ → Option α₂}
    {f_app₁ : α₁ → α₁ → σ₁ → Option α₁} {f_app₂ : α₂ → α₂ → σ₂ → Option α₂}
    {i₁ : σ₁} {i₂ : σ₂}
    {x₁ : α₁} {x₂ : α₂}
    :
    (t.accuM st_abs₁ st_app₁ z₁ zn₁ f_abs₁ f_app₁ i₁ = some x₁
      ∧ t.accuM st_abs₂ st_app₂ z₂ zn₂ f_abs₂ f_app₂ i₂ = some x₂)
    ↔
    (t.accuM
      (fun τ (s₁, s₂) => (st_abs₁ τ s₁, st_abs₂ τ s₂))
      (fun (s₁, s₂) => (((st_app₁ s₁).1, (st_app₂ s₂).1), ((st_app₁ s₁).2, (st_app₂ s₂).2)))
      (fun (s₁, s₂) => do (← z₁ s₁, ← z₂ s₂))
      (fun n (s₁, s₂) => do (← zn₁ n s₁, ← zn₂ n s₂))
      (fun τ (x₁, x₂) (s₁, s₂) => do (← f_abs₁ τ x₁ s₁, ← f_abs₂ τ x₂ s₂ ))
      (fun (x₁₁, x₁₂) (x₂₁, x₂₂) (s₁, s₂) => do (← f_app₁ x₁₁ x₂₁ s₁, ← f_app₂ x₁₂ x₂₂ s₂))
      (i₁, i₂) = some (x₁, x₂)) := by
    induction t generalizing i₁ i₂ x₁ x₂ <;> simp_all
    case unit =>
      apply Iff.intro <;> intro h <;> try simp_all
      -- (<-)
      generalize hy₁ : (z₁ i₁) = y₁
      generalize hy₂ : (z₂ i₂) = y₂
      cases y₁ <;> cases y₂ <;> simp_all
    case var n =>
      apply Iff.intro <;> intro h <;> try simp_all
      -- (<-)
      generalize hy₁ : (zn₁ n i₁) = y₁
      generalize hy₂ : (zn₂ n i₂) = y₂
      cases y₁ <;> cases y₂ <;> simp_all
    case abs τ t' ih =>
      apply Iff.intro
      . -- (->)
        intro ⟨ h₁, h₂ ⟩
        rw [Option.bind_eq_some_iff] at h₁ h₂
        replace ⟨ v₁, ⟨ hv₁, h₁ ⟩ ⟩ := @h₁
        replace ⟨ v₂, ⟨ hv₂, h₂ ⟩ ⟩ := @h₂
        replace ih := @ih (st_abs₁ τ i₁) (st_abs₂ τ i₂) v₁ v₂
        simp_all
      . -- (<-)
        intro h
        rw [Option.bind_eq_some_iff] at h
        replace ⟨ ⟨ v₁, v₂ ⟩ , ⟨ hv, h ⟩ ⟩ := h
        rw [Option.bind_eq_some_iff] at h
        replace ⟨ v₁', ⟨ hv₁' , h ⟩ ⟩ := h; simp_all
        rw [Option.bind_eq_some_iff] at h
        replace ⟨ v₂', ⟨ hv₂' , h ⟩ ⟩ := h; simp_all
        replace ih := @ih (st_abs₁ τ i₁) (st_abs₂ τ i₂) v₁ v₂
        simp_all
    case app t₁ t₂ ih₁ ih₂ =>
      apply Iff.intro
      . -- (->)
        intro ⟨ h₁, h₂ ⟩
        rw [Option.bind_eq_some_iff] at h₁ h₂
        replace ⟨ v₁₁, ⟨ hv₁₁, h₁ ⟩ ⟩ := @h₁
        replace ⟨ v₁₂, ⟨ hv₁₂, h₂ ⟩ ⟩ := @h₂
        rw [Option.bind_eq_some_iff] at h₁ h₂
        replace ⟨ v₂₁, ⟨ hv₂₁, h₁ ⟩ ⟩ := @h₁
        replace ⟨ v₂₂, ⟨ hv₂₂, h₂ ⟩ ⟩ := @h₂
        replace ih₁ := @ih₁ (st_app₁ i₁).1 (st_app₂ i₂).1 v₁₁ v₁₂
        replace ih₂ := @ih₂ (st_app₁ i₁).2 (st_app₂ i₂).2 v₂₁ v₂₂
        simp_all
      . -- (<-)
        intro h
        rw [Option.bind_eq_some_iff] at h
        replace ⟨ ⟨ v₁₁, v₁₂ ⟩ , ⟨ h₁, h ⟩ ⟩ := @h
        rw [Option.bind_eq_some_iff] at h
        replace ⟨ ⟨ v₂₁, v₂₂ ⟩ , ⟨ h₂, h ⟩ ⟩ := @h
        rw [Option.bind_eq_some_iff] at h
        replace ⟨ v₁, ⟨ hv₁ , h ⟩ ⟩ := h; simp_all
        rw [Option.bind_eq_some_iff] at h
        replace ⟨ v₂, ⟨ hv₂ , h ⟩ ⟩ := h; simp_all
        replace ih₁ := @ih₁ (st_app₁ i₁).1 (st_app₂ i₂).1 v₁₁ v₁₂
        replace ih₂ := @ih₂ (st_app₁ i₁).2 (st_app₂ i₂).2 v₂₁ v₂₂
        simp_all

end FoldMerging

namespace Palamedes

open Gen

namespace Gen

namespace CorrectGen

def Term.s_unfold
    {α σ : Type}
    {st_abs : Ty → σ → σ}
    {st_app : σ → σ × σ}
    {z : σ → Option α}
    {zn : Nat → σ → Option α}
    {f_abs : Ty → α → σ → Option α}
    {f_app : α → α → σ → Option α}
    {s : σ}
    {b : α}
    (g : (b : α) → (s : σ) → CorrectGen
      (fun (t : TermF α) =>
        (z s = some b ∧ t = .unit) ∨
        (∃ n, zn n s = some b ∧ t = .var n) ∨
        (∃ τ b', f_abs τ b' s = some b ∧ t = .abs τ b') ∨
        (∃ b₁ b₂, f_app b₁ b₂ s = some b ∧ t = .app b₁ b₂))) :
    CorrectGen (fun v => Term.accuM st_abs st_app z zn f_abs f_app v s = some b) :=
  Subtype.mk
    (Term.unfold (fun (b, s) => do
      match (← (g b s).val) with
      | .unit => pure .unit
      | .var n => pure (.var n)
      | .abs τ b' => pure (.abs τ (b', st_abs τ s) )
      | .app b₁ b₂ => pure (.app (b₁, (st_app s).1) (b₂, (st_app s).2))) (b, s)) <| by
    rw [Term.support_unfold]
    funext t
    induction t generalizing b s <;> simp_all
    case unit =>
      apply Iff.intro <;> intro h
      . replace ⟨ t', ⟨ ht', h ⟩ ⟩ := h
        cases t' <;> simp_all [(g b s).property]
      . exists TermF.unit
        simp_all [(g b s).property]
    case var n =>
      apply Iff.intro <;> intro h
      . replace ⟨ t', ⟨ ht', h ⟩ ⟩ := h
        cases t' <;> simp_all [(g b s).property]
      . exists TermF.var n
        simp_all [(g b s).property]
    case abs τ t' ih =>
      apply Iff.intro <;> intro h
      . replace ⟨ b', s', ⟨ ⟨ t'', ⟨ ht'' , h ⟩  ⟩, h' ⟩ ⟩ := h
        cases t'' <;> simp_all [(g b s).property]
      . rw [Option.bind_eq_some_iff] at h
        replace ⟨ b', ⟨ h', h ⟩ ⟩ := h
        exists b', st_abs τ s
        apply And.intro
        . exists TermF.abs τ b'
          simp_all [(g b s).property]
        . simp_all
    case app t₁ t₂ ih₁ ih₂ =>
      apply Iff.intro <;> intro h
      . replace ⟨ b₁, s₁, b₂, s₂, ⟨ ⟨ t', ⟨ ht' , h ⟩  ⟩, ⟨ h₁, h₂ ⟩ ⟩ ⟩ := h
        cases t' <;> simp_all [(g b s).property]
      . rw [Option.bind_eq_some_iff] at h
        replace ⟨ b₁, ⟨ h₁, h ⟩ ⟩ := h
        rw [Option.bind_eq_some_iff] at h
        replace ⟨ b₂, ⟨ h₂, h ⟩ ⟩ := h
        exists b₁, (st_app s).fst, b₂, (st_app s).snd
        apply And.intro
        . exists TermF.app b₁ b₂
          simp_all [(g b s).property]
        . simp_all

@[extract]
theorem Term.s_unfold_val
    {α σ : Type}
    {st_abs : Ty → σ → σ}
    {st_app : σ → σ × σ}
    {z : σ → Option α}
    {zn : Nat → σ → Option α}
    {f_abs : Ty → α → σ → Option α}
    {f_app : α → α → σ → Option α}
    {s : σ}
    {b : α}
    (g : (b : α) → (s : σ) → CorrectGen
      (fun (t : TermF α) =>
        (z s = some b ∧ t = .unit) ∨
        (∃ n, zn n s = some b ∧ t = .var n) ∨
        (∃ τ b', f_abs τ b' s = some b ∧ t = .abs τ b') ∨
        (∃ b₁ b₂, f_app b₁ b₂ s = some b ∧ t = .app b₁ b₂))) :
    (Term.s_unfold (st_abs := st_abs) (st_app := st_app) (s := s) (b := b) g).val
      = Term.unfold (fun (b, s) => do
          match (← (g b s).val) with
          | .unit => pure .unit
          | .var n => pure (.var n)
          | .abs τ b' => pure (.abs τ (b', st_abs τ s) )
          | .app b₁ b₂ => pure (.app (b₁, (st_app s).1) (b₂, (st_app s).2))) (b, s) := rfl

end CorrectGen

namespace Total

/-- An `unfold` whose step generator is everywhere assume-free is itself assume-free; the witness is
the same fixpoint at the failure-free interface. See `List.total_unfold`. -/
@[aesop safe (rule_sets := [totality])]
theorem Term.total_unfold
    (h : ∀ b, total (g b)) :
    total (Term.unfold g b) := by
  choose tg hg using h
  have : g = fun b => (tg b).toGen := funext fun b => (hg b).symm
  subst this
  exact ⟨TGen.Term.unfold tg b, by ext; rfl⟩

end Total

end Gen

end Palamedes

namespace PrettyPrint

def Term.toString : Term → String
  | .unit => "()"
  | .var n => s!"(var {n})"
  | .abs τ t => s!"({Ty.toString τ} → {Term.toString t})"
  | .app t₁ t₂ => s!"({Term.toString t₁} → {Term.toString t₂})"

instance : ToString Term where
  toString := Term.toString

end PrettyPrint
