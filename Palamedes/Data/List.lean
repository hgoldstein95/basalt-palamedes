import Palamedes.Gen
import Palamedes.OptimizeCongr
import Palamedes.CorrectGen
import Palamedes.Total
import Palamedes.Util

section BaseFunctor

inductive ListF (α β : Type) where
  | nil : ListF α β
  | cons : (a : α) → (b : β) → ListF α β

theorem ListF_or
    {α β : Type}
    {P : Prop}
    {Q : α → β → Prop}
    {t : ListF α β} :
    ListF.rec P Q t ↔ (P ∧ t = .nil) ∨ (∃ x b, t = .cons x b ∧ Q x b) := by
  match t with
  | .nil => simp
  | .cons x b => aesop

end BaseFunctor

section RecursionSchemes


def List.fold {α β: Type} (f : α → β → β) (z : β) (xs : List α) :=
  List.foldr f z xs

@[simp]
theorem List.fold_nil : List.fold f z .nil = z := rfl

@[simp]
theorem List.fold_cons
    {xs : List α}
    {f : α → β → β} :
    List.fold f z (.cons x xs) = f x (List.fold f z xs) :=
  rfl

def List.accuM
    [Monad m]
    {α β σ : Type}
    (st : α → σ → σ)
    (f : α → β → σ → m β)
    (z : σ → m β)
    (xs : List α)
    (s : σ) :
    m β :=
  match xs with
  | [] => z s
  | x :: xs => do f x (← List.accuM st f z xs (st x s)) s


@[simp]
theorem List.accuM_nil
    [Monad m]
    {st : α → σ → σ}
    {f : α → β → σ → m β}
    {z : σ → m β}
    {i : σ} :
    List.accuM st f z .nil i = z i :=
  rfl

@[simp]
theorem List.accuM_cons
    [Monad m]
    {st : α → σ → σ}
    {f : α → β → σ → m β}
    {z : σ → m β}
    {i : σ}
    {x: α}
    {xs : List α} :
    List.accuM st f z (.cons x xs) i = (do f x (← List.accuM st f z xs (st x i)) i) :=
  rfl

end RecursionSchemes

section Unfold

namespace Palamedes

open Gen

/-- The polymorphic Basalt generator underlying the list `unfold`: apply `step` to the seed; on `nil`
stop, on `cons x b'` emit `x` and recurse on `b'`. A direct `partial_fixpoint` over Basalt's CCPO.

`step` is the *already-instantiated* step generator (`β → G (ListF α β)`), not a `Gen`/`TGen`, so the
one fixpoint serves both the failure-supporting interface (`List.unfold`, via `(f b).run`) and the
failure-free one (`TGen.List.unfold`); their totality relationship is then a fixpoint congruence (see
`List.total_unfold`). -/
def List.unfoldGo [_root_.Gen G] (step : β → G (ListF α β)) (b : β) : G (List α) :=
  step b >>= fun t =>
    match t with
    | .nil => pure []
    | .cons x b' => List.unfoldGo step b' >>= fun xs => pure (x :: xs)
  partial_fixpoint

/-- The recursive list `unfold` operator. Synthesis emits applications of this as data; the recursion
lives in the `partial_fixpoint` `unfoldGo`. -/
def List.unfold (f : β → Gen (ListF α β)) (b : β) : Gen (List α) :=
  ⟨fun {_G} _ _ => List.unfoldGo (fun b => (f b).run) b⟩

/-- The failure-free list `unfold`: the same fixpoint instantiated at a `TGen` step. This is the
totality witness for `List.unfold` when its step is failure-free. -/
def TGen.List.unfold (f : β → TGen (ListF α β)) (b : β) : TGen (List α) :=
  ⟨fun {_G} _ => Palamedes.List.unfoldGo (fun b => (f b).run) b⟩

@[simp]
theorem List.run_unfold (f : β → Gen (ListF α β)) (b : β) (G : Type → Type) [_root_.Gen G] [Fail G] :
    (List.unfold f b).run (G := G) = List.unfoldGo (fun b => (f b).run) b := rfl

-- TODO: I wish I had a better naming convention for this.
@[simp]
def List.unfold_support (P : β → ListF α β → Prop) (b : β) (xs : List α) : Prop :=
  match xs with
  | [] => P b .nil
  | x :: xs => ∃ b', P b (.cons x b') ∧ List.unfold_support P b' xs

@[simp]
theorem List.support_unfold :
    support (List.unfold f b) = List.unfold_support (fun b' => support (f b')) b := by
  funext xs
  apply propext
  show xs ∈ SPMF.support (List.unfoldGo (fun b => (f b).run) b) ↔
    List.unfold_support (fun b' => support (f b')) b xs
  induction xs generalizing b with
  | nil =>
    unfold List.unfoldGo
    rw [SPMF.support_bind]
    simp only [Set.mem_setOf_eq, List.unfold_support]
    constructor
    · rintro ⟨t, ht, hxs⟩
      cases t with
      | nil => exact ht
      | cons x b' => simp at hxs
    · intro h
      exact ⟨.nil, h, by simp⟩
  | cons x xs ih =>
    unfold List.unfoldGo
    rw [SPMF.support_bind]
    simp only [Set.mem_setOf_eq, List.unfold_support]
    constructor
    · rintro ⟨t, ht, hxs⟩
      cases t with
      | nil => simp [SPMF.support_pure] at hxs
      | cons x' b' =>
        simp only [SPMF.support_bind, SPMF.support_pure, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at hxs
        obtain ⟨ys, hys, heq⟩ := hxs
        obtain ⟨rfl, rfl⟩ := List.cons.inj heq.symm
        exact ⟨b', ht, ih.mp hys⟩
    · rintro ⟨b', hb', hxs⟩
      refine ⟨.cons x b', hb', ?_⟩
      simp only [SPMF.support_bind, SPMF.support_pure, Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨xs, ih.mpr hxs, rfl⟩

@[gen_congr]
theorem List.support_unfold_congr
    {hf : ∀ {b}, support (f b) = support (f' b)} :
    support (List.unfold f b) = support (List.unfold f' b) := by
  aesop

end Palamedes

end Unfold

section FoldConversions

theorem List.fold_accu_Option_basic
    {α β : Type}
    {v : β}
    {xs : List α}
    {z : β}
    {f : α → β → β} :
    List.fold f z xs = v ↔
    List.accuM
      (fun _ _ => ())
      (fun x b _ => some (f x b))
      (fun _ => some z)
      xs
      () = some v := by
  induction xs generalizing v <;> simp_all [List.fold, List.accuM]
  case cons x xs' ih =>
    replace ih := @ih (List.fold f z xs')
    simp_all [List.fold]

theorem List.fold_accu_Option_true
    {α : Type}
    {xs : List α}
    {g : α → Bool}
    {f :  α → Bool → Bool}
    (h : ∀ x acc, f x acc = (g x && acc)) :
    List.fold f true xs = true ↔
    List.accuM
      (fun _ _ => ())
      (fun x _ _ => guard (g x))
      (fun _ => some ())
      xs
      () = some () := by
  induction xs <;> simp_all [List.fold, List.accuM]
  case cons x xs' ih =>
    apply Iff.intro <;> intro hf
    . generalize hv : fold f true xs' = v
      cases v <;>
        simp_all [List.fold, guard]
    . rw [Option.bind_eq_some_iff] at hf
      replace ⟨ v, hf ⟩ := hf
      simp_all [guard]

theorem List.fold_accu_Option_function
    {α β σ : Type}
    {i : σ}
    {v : β}
    {xs : List α}
    {z : (σ → β)}
    {f : α → (σ → β) → (σ → β)}
    {g : α → β → σ → Option β}
    {st :  α → σ → σ}
    (h : ∀ x acc s w, f x acc s = w ↔ (do g x (← acc (st x s)) s) = some w) :
    List.fold f z xs i = v ↔
    List.accuM
      st
      g
      (fun s => some (z s))
      xs
      i = some v := by
  induction xs generalizing v i <;> simp_all [List.fold, List.accuM, Option.bind_eq_some_iff]
  case cons x xs' ih =>
    apply Iff.intro <;> intro hg
    . exists (foldr f z xs' (st x i))
      simp_all
      rw [← ih]
    . replace ⟨w, ⟨hgw, hg⟩⟩ := hg
      rw [← ih] at hgw
      rw [hgw]
      apply hg

theorem List.fold_accu_Option_function_true
    {α σ : Type}
    {i : σ}
    {xs : List α}
    {f : α → (σ → Bool) → (σ → Bool)}
    {g : α → σ → Bool}
    {st :  α → σ → σ}
    (h : ∀ x acc s,
      f x acc s = true ↔ (do (return (g x s) && (← acc (st x s)))) = some true)
    :
    List.fold f (fun _ => true) xs i = true ↔
    List.accuM
      st
      (fun x _ s => guard $ g x s)
      (fun _ => some ())
      xs
      i = some () := by
    induction xs generalizing i <;> simp_all [List.fold, List.accuM, Option.bind_eq_some_iff, guard]
    case cons x xs' ih =>
      apply Iff.intro <;> intro hg <;> simp_all
      replace ⟨⟨v, hv ⟩ , hg⟩ := hg; simp_all

theorem List.fold_accu_cond
  {α σ : Type}
  {i : σ}
  {stTrue stFalse : α -> σ -> σ}
  {condTrue condFalse initCond : σ -> Bool}
  {xs : List α}
  {condGuard : α -> σ -> Bool} :
  List.fold
    (fun x acc s => if condGuard x s = true then
                      condTrue s && acc (stTrue x s) else
                      condFalse s && acc (stFalse x s))
    (fun s => initCond s)
    xs
    i = true ↔
  List.accuM
    (fun x s => if condGuard x s then stTrue x s else stFalse x s)
    (fun x _ s =>
      if condGuard x s then guard $ condTrue s else guard $ condFalse s)
    (fun s => guard $ initCond s)
    (xs : List α)
    i = some () := by
  induction xs generalizing i <;> simp_all [List.fold, List.accuM, Option.bind_eq_some_iff, guard]
  case cons head tail ih =>
    cases (condGuard head i) <;> aesop

end FoldConversions

section FoldCoercion

theorem List.coerce_to_fold
    {xs : List α}
    {f : List α → β}
    {z : β}
    {g : α → β → β}
    (h1 : f [] = z := by rflm)
    (h2 : ∀ x xs, f (x :: xs) = g x (f xs)
      := by intros; simp_all [- Bool.not_eq_eq_eq_not]; rflm) :
    f xs = xs.fold g z := by
  induction xs <;> simp_all

end FoldCoercion

section FoldMerging

theorem List.merge_accuM
    {xs : List α}
    {st₁ : α → σ₁ → σ₁}
    {st₂ : α → σ₂ → σ₂}
    {f₁ : α → β₁ → σ₁ → Option β₁}
    {f₂ : α → β₂ → σ₂ → Option β₂}
    {s₁ : σ₁} {s₂ : σ₂}
    {z₁ : σ₁ → Option β₁} {z₂ : σ₂ → Option β₂}
    {b₁ : β₁} {b₂ : β₂} :
    (xs.accuM st₁ f₁ z₁ s₁ = some b₁ ∧ xs.accuM st₂ f₂ z₂ s₂ = some b₂)
    ↔
    (xs.accuM
      (fun x (s₁, s₂) => (st₁ x s₁, st₂ x s₂))
      (fun x (b₁, b₂) (s₁, s₂) => do (← f₁ x b₁ s₁, ← f₂ x b₂ s₂))
      (fun (s₁, s₂) => do (← z₁ s₁, ← z₂ s₂))
      (s₁, s₂) = some (b₁, b₂)) := by
  induction xs generalizing st₁ st₂ f₁ f₂ s₁ s₂ z₁ z₂ b₁ b₂
  case nil => simp_all [List.accuM, Option.bind_eq_some_iff]
  case cons y ys ih =>
    simp_all [List.accuM, Option.bind_eq_some_iff]
    apply Iff.intro
    . -- (->)
      intro ⟨ ⟨ v₁, ⟨ hv1h, hv1tl ⟩ ⟩ , ⟨ v₂, ⟨ hv2h, hv2tl ⟩ ⟩ ⟩
      exists v₁, v₂
      replace ih := @ih st₁ st₂ f₁ f₂ (st₁ y s₁) (st₂ y s₂) z₁ z₂ v₁ v₂
      simp_all
    . -- (<-)
      intro ⟨ v₁, v₂, h, h1, h2 ⟩
      replace ih := @ih st₁ st₂ f₁ f₂ (st₁ y s₁) (st₂ y s₂) z₁ z₂ v₁ v₂
      apply And.intro
      . exists v₁
        simp_all
      . exists v₂
        simp_all

end FoldMerging

namespace Palamedes

open Gen

namespace Gen

namespace CorrectGen

def List.s_unfold
    {α β σ : Type}
    {st : α → σ → σ}
    {f : α → β → σ → Option β}
    {z : σ → Option β}
    {s : σ}
    {b : β}
    (g : (b : β) → (s : σ) → CorrectGen
      (fun (t : ListF α β) =>
        (z s = some b ∧ t = .nil) ∨
        (∃ a b', f a b' s = some b ∧ t = .cons a b'))) :
    CorrectGen (fun v => List.accuM st f z v s = some b) :=
  Subtype.mk
    (List.unfold (fun (b, s) => do
      match (← (g b s).val) with
      | .nil => pure .nil
      | .cons x b' => pure (.cons x (b', st x s))) (b, s)) <| by
    rw [List.support_unfold]
    funext xs
    induction xs generalizing b s <;> simp_all
    case nil =>
      apply Iff.intro <;> intro h
      . replace ⟨ ys, ⟨ hys, h ⟩ ⟩ := h
        cases ys <;> simp_all [(g b s).property]
      . exists ListF.nil
        simp_all [(g b s).property]
    case cons x xs ih =>
      apply Iff.intro <;> intro h
      . replace ⟨ b', ⟨ s', ⟨ ⟨ ys, ⟨ hys, h ⟩ ⟩ , h' ⟩ ⟩ ⟩ := h
        cases ys <;> simp_all [(g b s).property]
      . rw [Option.bind_eq_some_iff] at h
        replace ⟨ b', ⟨ hxs, h ⟩ ⟩ := h
        exists b', st x s
        apply And.intro
        . exists ListF.cons x b'
          simp_all [(g b s).property]
        . assumption

@[extract]
theorem List.s_unfold_val
    {α β σ : Type}
    {st : α → σ → σ}
    {f : α → β → σ → Option β}
    {z : σ → Option β}
    {s : σ}
    {b : β}
    (g : (b : β) → (s : σ) → CorrectGen
      (fun (t : ListF α β) =>
        (z s = some b ∧ t = .nil) ∨
        (∃ a b', f a b' s = some b ∧ t = .cons a b'))) :
    (List.s_unfold (st := st) (s := s) (b := b) g).val
      = List.unfold (fun (b, s) => do
          match (← (g b s).val) with
          | .nil => pure .nil
          | .cons x b' => pure (.cons x (b', st x s))) (b, s) := rfl

end CorrectGen

namespace Total

/-- An `unfold` whose step generator is everywhere assume-free is itself assume-free. The witness is
the *same* `unfoldGo` fixpoint re-run at the failure-free interface (`TGen.List.unfold`); since
`unfoldGo` never mentions `Fail`, the two coincide by a fixpoint congruence (here: definitional,
because `TGen.toGen` forgets the `Fail` instance argument). -/
@[aesop safe (rule_sets := [totality])]
theorem List.total_unfold
    (h : ∀ b, total (g b)) :
    total (List.unfold g b) := by
  choose tg hg using h
  have : g = fun b => (tg b).toGen := funext fun b => (hg b).symm
  subst this
  exact ⟨TGen.List.unfold tg b, by ext; rfl⟩

end Total

end Gen

end Palamedes
