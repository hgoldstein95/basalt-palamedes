import Palamedes.Gen
import Palamedes.OptimizeCongr
import Palamedes.CorrectGen
import Palamedes.Total
import Palamedes.Util

-- Lean core (v4.32+) declares a deprecated `Tree` (alias for `BinaryTree`) at the root namespace, so
-- Palamedes' own `Tree` lives under `namespace Palamedes` to avoid the clash.
namespace Palamedes

section TypeDef

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : (l : Tree α) → (x : α) → (r : Tree α) → Tree α
deriving Repr

end TypeDef

section BaseFunctor

inductive TreeF (α β : Type) where
  | leaf : TreeF α β
  | node : (l : β) → (x : α) → (r : β) → TreeF α β

theorem TreeF_or
    {α β : Type}
    {P : Prop}
    {Q : β → α → β → Prop}
    {t : TreeF α β} :
    TreeF.rec P Q t ↔ (P ∧ t = .leaf) ∨ (∃ bl x br, t = .node bl x br ∧ Q bl x br) := by
  match t with
  | .leaf => simp
  | .node _ _ _ => aesop

end BaseFunctor

section RecursionSchemes

def Tree.fold
    {α β : Type}
    (f : β → α → β → β)
    (z : β)
    (t : Tree α) :
    β :=
  match t with
  | .leaf => z
  | .node l x r => f (Tree.fold f z l) x (Tree.fold f z r)

@[simp] theorem Tree.fold_leaf : Tree.fold f z .leaf = z := rfl
@[simp] theorem Tree.fold_node {x} {l r : Tree α} {f : β → α → β → β} {z} :
    Tree.fold f z (.node l x r) = f (Tree.fold f z l) x (Tree.fold f z r) := rfl

def Tree.accuM
    [Monad m]
    {α β σ : Type}
    (st : α → σ → σ × σ)
    (f : β → α → β → σ → m β)
    (z : σ → m β)
    (t : Tree α)
    (i : σ) :
    m β :=
  match t with
  | .leaf => z i
  | .node l x r => do
    let (sl, sr) := st x i
    f (← Tree.accuM st f z l sl) x (← Tree.accuM st f z r sr) i

@[simp] theorem Tree.accuM_leaf
  [Monad m] {α σ} {st : α → σ → σ × σ} {f : β → α → β → σ → m β} {z : σ → m β} {i : σ} :
  Tree.accuM st f z (.leaf : Tree α) i = z i := rfl
@[simp] theorem Tree.accuM_node
  [Monad m] {α σ} {st : α → σ → σ × σ} {f : β → α → β → σ → m β} {z : σ → m β} {i : σ} {x} {l r : Tree α} :
  Tree.accuM st f z (.node l x r) i =
   (do
    let (sl, sr) := st x i
    f (← Tree.accuM st f z l sl) x (← Tree.accuM st f z r sr) i) := by rfl

end RecursionSchemes

section Unfold

open Gen

/-- The polymorphic Basalt generator underlying the tree `unfold`: `leaf` stops, `node bl x br`
recurses on both children. A direct `partial_fixpoint`. -/
def Tree.unfoldGo [_root_.Gen G] (step : β → G (TreeF α β)) (b : β) : G (Tree α) :=
  step b >>= fun t =>
    match t with
    | .leaf => pure .leaf
    | .node bl x br =>
      Tree.unfoldGo step bl >>= fun l =>
      Tree.unfoldGo step br >>= fun r =>
      pure (.node l x r)
  partial_fixpoint

def Tree.unfold (f : β → Gen (TreeF α β)) (v : β) : Gen (Tree α) :=
  ⟨fun {_G} _ _ => Tree.unfoldGo (fun b => (f b).run) v⟩

/-- Failure-free witness for `Tree.unfold`: the same fixpoint at the `Fail`-free interface. -/
def TGen.Tree.unfold (f : β → TGen (TreeF α β)) (v : β) : TGen (Tree α) :=
  ⟨fun {_G} _ => Palamedes.Tree.unfoldGo (fun b => (f b).run) v⟩

@[simp]
def Tree.unfold_support (P : β → TreeF α β → Prop) (b : β) (t : Tree α) : Prop :=
  match t with
  | .leaf => P b .leaf
  | .node l x r => ∃ bl br,
    P b (.node bl x br) ∧
    Tree.unfold_support P bl l ∧
    Tree.unfold_support P br r

@[simp]
theorem Tree.support_unfold :
    support (Tree.unfold f b) = Tree.unfold_support (fun b' => support (f b')) b := by
  funext s
  apply propext
  show s ∈ SPMF.support (Tree.unfoldGo (fun b => (f b).run) b) ↔
    Tree.unfold_support (fun b' => support (f b')) b s
  induction s generalizing b with
  | leaf =>
    unfold Tree.unfoldGo
    rw [SPMF.support_bind]
    simp only [Set.mem_setOf_eq, Tree.unfold_support]
    constructor
    · rintro ⟨t, ht, hxs⟩
      cases t with
      | leaf => exact ht
      | node bl x br => simp at hxs
    · intro h
      exact ⟨.leaf, h, by simp⟩
  | node l x r ihl ihr =>
    unfold Tree.unfoldGo
    rw [SPMF.support_bind]
    simp only [Set.mem_setOf_eq, Tree.unfold_support]
    constructor
    · rintro ⟨t, ht, hxs⟩
      cases t with
      | leaf => simp at hxs
      | node bl x' br =>
        simp only [SPMF.support_bind, SPMF.support_pure, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at hxs
        obtain ⟨l', hl', r', hr', heq⟩ := hxs
        obtain ⟨rfl, rfl, rfl⟩ := Tree.node.inj heq.symm
        exact ⟨bl, br, ht, ihl.mp hl', ihr.mp hr'⟩
    · rintro ⟨bl, br, hb', hl, hr⟩
      refine ⟨.node bl x br, hb', ?_⟩
      simp only [SPMF.support_bind, SPMF.support_pure, Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨l, ihl.mpr hl, r, ihr.mpr hr, rfl⟩

@[gen_congr]
theorem Tree.support_unfold_congr
    {hf : ∀ {b}, support (f b) = support (f' b)} :
    support (Tree.unfold f b) = support (Tree.unfold f' b) := by
  aesop

end Unfold

section FoldConversions

theorem Tree.fold_accu_Option_basic
    {α β : Type}
    {v : β}
    {t : Tree α}
    {z : β}
    {f : β → α → β → β} :
    Tree.fold f z t = v ↔
    Tree.accuM
      (fun _ _ => ((), ()))
      (fun l x r _ => some (f l x r))
      (fun _ => some z)
      t
      () = some v := by
    induction t generalizing v <;> simp_all [Tree.fold, Tree.accuM]
    case node l x r ihl ihr =>
        replace ihl := @ihl (Tree.fold f z l)
        replace ihr := @ihr (Tree.fold f z r)
        simp_all

theorem Tree.fold_accu_Option_true
    {α : Type}
    {t : Tree α}
    {g : α → Bool}
    {f : Bool → α → Bool → Bool}
    (h : ∀ accL x accR, f accL x accR = (g x && accL && accR)) :
    Tree.fold f true t = true ↔
    Tree.accuM
      (fun _ _ => ((), ()))
      (fun _ x _ _ => guard (g x))
      (fun _ => some ())
      t
      () = some () := by
    induction t <;> simp_all [Tree.fold, Tree.accuM]
    case node l x r ihl ihr =>
        apply Iff.intro <;> intro hf
        . -- (->)
          generalize hvl : fold f true l = vl
          generalize hvr : fold f true r = vr
          cases vl <;> cases vr <;>
            simp_all [guard]
        . -- (<-)
          rw [Option.bind_eq_some_iff] at hf
          replace ⟨ vl, hf ⟩ := hf
          rw [Option.bind_eq_some_iff] at hf
          replace ⟨ h1, ⟨ v, h2 ⟩ ⟩ := hf
          simp_all [guard]

theorem Tree.fold_accu_Option_function
    {α β σ : Type}
    {i : σ}
    {v : β}
    {t : Tree α}
    {z : (σ → β)}
    {f : (σ → β) → α → (σ → β) → (σ → β)}
    {g : β → α → β → σ → Option β}
    {stl str :  α → σ → σ}
    (h : ∀ accL x accR s w,
      f accL x accR s = w ↔ (do g (← accL (stl x s)) x (← accR (str x s)) s) = some w)
    :
    Tree.fold f z t i = v ↔
    Tree.accuM
      (fun x s => (stl x s, str x s))
      g
      (fun s => some (z s))
      t
      i = some v := by
    induction t generalizing v i <;> simp_all [Tree.fold, Tree.accuM, Option.bind_eq_some_iff]
    case node l x r ihl ihr =>
      apply Iff.intro <;> intro hg
      . -- (->)
        exists (Tree.fold f z l (stl x i))
        rw [← ihl]
        simp_all
        exists (Tree.fold f z r (str x i))
        rw [← ihr]
        simp_all
      . -- (<-)
        replace ⟨ vl, hl, vR, hr, hg ⟩ := hg
        rw [← ihl] at hl
        rw [← ihr] at hr
        rw [hl, hr]
        apply hg

theorem Tree.fold_accu_Option_function_true
    {α σ : Type}
    {i : σ}
    {t : Tree α}
    {z : σ → Bool}
    {f : (σ → Bool) → α → (σ → Bool) → (σ → Bool)}
    {g : α → σ → Bool}
    {stL stR :  α → σ → σ}
    (h : ∀ accL x accR s,
      f accL x accR s = true ↔ (do (return (g x s) && (← accL (stL x s)) && (← accR (stR x s)))) = some true)
    :
    Tree.fold f z t i = true ↔
    Tree.accuM
      (fun x s => (stL x s, stR x s))
      (fun _ x _ s => guard $ g x s)
      (fun s => guard (z s))
      t
      i = some () := by
    induction t generalizing i <;> simp_all [Tree.fold, Tree.accuM, Option.bind_eq_some_iff, guard]
    case node l x r ihl ihr =>
      apply Iff.intro <;> intro hg <;> simp_all
      replace ⟨⟨ vl, hl ⟩, ⟨ vr, hr ⟩ , hg⟩ := hg; simp_all

theorem Tree.fold_accu_cond
  {α σ : Type}
  {i : σ}
  {stTrue stFalse : α -> σ -> σ}
  {condTrue condFalse initCond : σ -> Bool}
  {t : Tree α}
  {condGuard : α -> σ -> Bool} :
  Tree.fold
    (fun accL x accR s => if condGuard x s then
                      condTrue s && accL (stTrue x s) && accR (stTrue x s) else
                      condFalse s && accL (stFalse x s) && accR (stFalse x s))
    (fun s => initCond s)
    t
    i = true ↔
  Tree.accuM
    (fun x s => if condGuard x s then (stTrue x s, stTrue x s) else (stFalse x s, stFalse x s))
    (fun _ x _ s =>
      if condGuard x s then guard $ condTrue s else guard $ condFalse s)
    (fun s => guard $ initCond s)
    t
    i = some () := by
    induction t generalizing i <;> simp_all [Tree.fold, Tree.accuM, Option.bind_eq_some_iff, guard]
    case node l v r ihl ihr =>
      cases (condGuard v i) <;> aesop

end FoldConversions

section FoldCoercion

theorem Tree.coerce_to_fold
    {t : Tree α}
    {f : Tree α → β} -- function to be coerced
    {z : β}
    {g : β → α → β → β}
    (h1 : f .leaf = z := by aesop)
    (h2 : ∀ l x r, f (.node l x r) = g (f l) x (f r)
      := by intros; simp_all; rflm) :
    f t = t.fold g z := by
  induction t <;> simp_all

end FoldCoercion

section FoldMerging

theorem Tree.merge_accuM
    {t : Tree α}
    {st₁ : α → σ₁ → σ₁ × σ₁}
    {st₂ : α → σ₂ → σ₂ × σ₂}
    {f₁ : β₁ → α → β₁ → σ₁ → Option β₁}
    {f₂ : β₂ → α → β₂ → σ₂ → Option β₂}
    {s₁ : σ₁} {s₂ : σ₂}
    {z₁ : σ₁ → Option β₁} {z₂ : σ₂ → Option β₂}
    {b₁ : β₁} {b₂ : β₂}
    :
    (t.accuM st₁ f₁ z₁ s₁ = some b₁ ∧ t.accuM st₂ f₂ z₂ s₂ = some b₂)
    ↔
    (t.accuM
      (fun x (s₁, s₂) => (((st₁ x s₁).1, (st₂ x s₂).1), ((st₁ x s₁).2, (st₂ x s₂).2)))
      (fun (bl₁, bl₂) x (br₁, br₂) (s₁, s₂) => do (← f₁ bl₁ x br₁ s₁, ← f₂ bl₂ x br₂ s₂))
      (fun (s₁, s₂) => do (← z₁ s₁, ← z₂ s₂))
      (s₁, s₂) = some (b₁, b₂)) := by
  induction t generalizing st₁ st₂ f₁ f₂ s₁ s₂ z₁ z₂ b₁ b₂
  case leaf =>
    simp [accuM]
    apply Iff.intro <;> intro H
    . -- (->)
      rw [H.left, H.right]
      simp
    . -- (<-)
      generalize Hx1 : (z₁ s₁) = x1
      generalize Hx2 : (z₂ s₂) = x2
      cases x1 <;> cases x2 <;> simp_all
  case node l x r IHl IHr =>
    apply Iff.intro
    . -- (->)
      intro ⟨ H1, H2 ⟩
      unfold accuM at H1 H2 ⊢
      simp at H1 H2 ⊢
      rw [Option.bind_eq_some_iff] at H1 H2
      replace ⟨ lv₁, ⟨ Hlv₁, H1 ⟩  ⟩ := @H1
      replace ⟨ lv₂, ⟨ Hlv₂, H2 ⟩  ⟩ := @H2
      rw [Option.bind_eq_some_iff] at H1 H2
      replace ⟨ rv₁, ⟨ Hrv₁, H1 ⟩  ⟩ := @H1
      replace ⟨ rv₂, ⟨ Hrv₂, H2 ⟩  ⟩ := @H2
      replace IHl := @IHl st₁ st₂ f₁ f₂ (st₁ x s₁).fst (st₂ x s₂).fst z₁ z₂ lv₁ lv₂
      replace IHr := @IHr st₁ st₂ f₁ f₂ (st₁ x s₁).snd (st₂ x s₂).snd z₁ z₂ rv₁ rv₂
      simp_all
    . -- (<-)
      intro H
      unfold accuM at H ⊢
      simp at H ⊢
      rw [Option.bind_eq_some_iff] at H
      replace ⟨ ⟨ lv₁, lv₂ ⟩ , ⟨ Hlv, H ⟩  ⟩ := @H
      rw [Option.bind_eq_some_iff] at H
      replace ⟨ ⟨ rv₁, rv₂ ⟩ , ⟨ Hrv, H ⟩ ⟩ := @H
      rw [Option.bind_eq_some_iff] at H
      replace ⟨ v₁, ⟨ Hv₁ , H ⟩ ⟩ := @H
      rw [Option.bind_eq_some_iff] at H
      replace ⟨ v₂, ⟨ Hv₂ , H ⟩ ⟩ := @H
      replace IHl := @IHl st₁ st₂ f₁ f₂ (st₁ x s₁).fst (st₂ x s₂).fst z₁ z₂ lv₁ lv₂
      replace IHr := @IHr st₁ st₂ f₁ f₂ (st₁ x s₁).snd (st₂ x s₂).snd z₁ z₂ rv₁ rv₂
      simp_all

end FoldMerging

open Gen

namespace Gen

namespace CorrectGen

def Tree.s_unfold
    {α β σ : Type}
    {st : α → σ → σ × σ}
    {f : β → α → β → σ → Option β}
    {z : σ → Option β}
    {s : σ}
    {b : β}
    (g : (b : β) → (s : σ) → CorrectGen
      (fun (t : TreeF α β) =>
        (z s = some b ∧ t = .leaf) ∨
        (∃ a bl br, f bl a br s = some b ∧ t = .node bl a br))) :
    CorrectGen (fun v => Tree.accuM st f z v s = some b) :=
  Subtype.mk
    (Tree.unfold (fun (b, s) => do
      match (← (g b s).val) with
      | .leaf => pure .leaf
      | .node bl x br => pure (.node (bl, (st x s).1) x (br, (st x s).2))) (b, s)) <| by
    rw [Tree.support_unfold]
    funext t
    induction t generalizing b s <;> simp_all
    case leaf =>
      apply Iff.intro <;> intro h
      . replace ⟨ t', ⟨ ht', h ⟩ ⟩ := h
        cases t' <;> simp_all [(g b s).property]
      . exists TreeF.leaf
        simp_all [(g b s).property]
    case node l x r ihl ihr =>
      apply Iff.intro <;> intro h
      . replace ⟨ bl, sl, br, sr, ⟨ ⟨ t', ⟨ ht' , h ⟩  ⟩, ⟨ hl, hr ⟩ ⟩ ⟩ := h
        cases t' <;> simp_all [(g b s).property]
      . rw [Option.bind_eq_some_iff] at h
        replace ⟨ bl, ⟨ hl, h ⟩ ⟩ := h
        rw [Option.bind_eq_some_iff] at h
        replace ⟨ br, ⟨ hr, h ⟩ ⟩ := h
        exists bl, (st x s).fst, br, (st x s).snd
        apply And.intro
        . exists TreeF.node bl x br
          simp_all [(g b s).property]
        . simp_all

@[extract]
theorem Tree.s_unfold_val
    {α β σ : Type}
    {st : α → σ → σ × σ}
    {f : β → α → β → σ → Option β}
    {z : σ → Option β}
    {s : σ}
    {b : β}
    (g : (b : β) → (s : σ) → CorrectGen
      (fun (t : TreeF α β) =>
        (z s = some b ∧ t = .leaf) ∨
        (∃ a bl br, f bl a br s = some b ∧ t = .node bl a br))) :
    (Tree.s_unfold (st := st) (s := s) (b := b) g).val
      = Tree.unfold (fun (b, s) => do
          match (← (g b s).val) with
          | .leaf => pure .leaf
          | .node bl x br => pure (.node (bl, (st x s).1) x (br, (st x s).2))) (b, s) := rfl

end CorrectGen

namespace Total

/-- An `unfold` whose step generator is everywhere assume-free is itself assume-free; the witness is
the same fixpoint at the failure-free interface. See `List.total_unfold`. -/
@[aesop safe (rule_sets := [totality])]
theorem Tree.total_unfold
    (h : ∀ b, total (g b)) :
    total (Tree.unfold g b) := by
  choose tg hg using h
  have : g = fun b => (tg b).toGen := funext fun b => (hg b).symm
  subst this
  exact ⟨TGen.Tree.unfold tg b, by ext; rfl⟩

end Total

end Gen

namespace PrettyPrint

def Tree.toString [ToString α] : Tree α → String
  | .leaf => "(leaf)"
  | .node l x r => s!"(node {Tree.toString l} {x} {Tree.toString r})"

instance [ToString α] : ToString (Tree α) where
  toString := Tree.toString

end PrettyPrint

end Palamedes
