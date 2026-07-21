import Palamedes.Derive

/-!
# `derive_palamedes` tests

Exercises the derive command on three constructor shapes — binary recursion with a parameter
(`MyTree`), unary recursion (`MyList`), and a parameter-free type mixing non-recursive payloads
(`Nat`, `Bool`) with unary/binary/ternary recursion (`Expr`) — and checks:

* every generated declaration exists at its expected type (the `example := @X.decl` lines fail
  to elaborate on any signature drift);
* the generated proofs use no extra axioms (in particular no `sorryAx`);
* the generated `@[simp]` equations actually compute;
* unsupported shapes (nested recursion) are rejected with a clear error.
-/

namespace DeriveTest

inductive MyTree (α : Type) where
  | leaf
  | node (l : MyTree α) (x : α) (r : MyTree α)

inductive MyList (α : Type) where
  | nil
  | cons (x : α) (xs : MyList α)

inductive Expr where
  | lit (n : Nat)
  | neg (e : Expr)
  | add (l : Expr) (r : Expr)
  | ite3 (c : Expr) (t : Expr) (e : Expr) (tag : Bool)

end DeriveTest

derive_palamedes DeriveTest.MyTree
derive_palamedes DeriveTest.MyList
derive_palamedes DeriveTest.Expr

namespace DeriveTest

open Palamedes Palamedes.PGen

-- ── signatures of the generated declarations ──

example : {α β : Type} → β → (β → α → β → β) → MyTree α → β := @MyTree.fold

example : {m : Type → Type} → [Monad m] → {α β σ : Type} →
    (α → σ → σ × σ) → (σ → m β) → (β → α → β → σ → m β) → MyTree α → σ → m β :=
  @MyTree.accuM

-- The recursion threads a `Nat` depth: `unfoldGo` hands it to the step and unfolds children at
-- `d + 1`, while `unfold` takes a starting depth defaulting to `0`. The seed type is unchanged.

example : {G : Type → Type} → [Gen G] → {α β : Type} →
    (Nat → β → G (MyTreeF α β)) → Nat → β → G (MyTree α) :=
  @MyTree.unfoldGo

example : {α β : Type} → (Nat → β → PGen (MyTreeF α β)) → β → Nat → PGen (MyTree α) := @MyTree.unfold

example : {α β : Type} → (Nat → β → TGen (MyTreeF α β)) → β → Nat → TGen (MyTree α) :=
  @TGen.MyTree.unfold

-- the starting depth is an optional argument: existing call sites are untouched
example {α β : Type} (f : Nat → β → PGen (MyTreeF α β)) (b : β) :
    MyTree.unfold f b = MyTree.unfold f b 0 := rfl

example : {α β : Type} → (Nat → β → MyTreeF α β → Prop) → Nat → β → MyTree α → Prop :=
  @MyTree.unfold_support

-- `support_unfold` is unconditional: no depth-independence hypothesis is needed to state it.
example : ∀ {α β : Type} {f : Nat → β → PGen (MyTreeF α β)} {b : β} {d₀ : Nat},
    support (MyTree.unfold f b d₀)
      = MyTree.unfold_support (fun d x => support (f d x)) d₀ b :=
  @MyTree.support_unfold

example : ∀ {α β : Type} {f f' : Nat → β → PGen (MyTreeF α β)} {b : β} {d₀ : Nat},
    (∀ {d x}, support (f d x) = support (f' d x)) →
    support (MyTree.unfold f b d₀) = support (MyTree.unfold f' b d₀) :=
  fun h => MyTree.support_unfold_congr h

example : ∀ {α β : Type} {g : Nat → β → PGen (MyTreeF α β)} {b : β} {d₀ : Nat},
    (∀ d x, total (g d x)) → total (MyTree.unfold g b d₀) :=
  fun h => MyTree.total_unfold h

-- ── the generated proofs are axiom-clean (no `sorryAx`) ──

/-- info: 'DeriveTest.MyTree.support_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MyTree.support_unfold

/-- info: 'DeriveTest.Expr.support_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Expr.support_unfold

/-- info: 'DeriveTest.Expr.coerce_to_fold' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Expr.coerce_to_fold

/-- info: 'DeriveTest.Expr.total_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Expr.total_unfold

-- ── the generated equations compute ──

example : MyList.fold (β := Nat) 0 (fun _ n => n + 1) (.cons 7 (.cons 8 .nil)) = 2 := by simp

example :
    Expr.fold (fun n => n) (fun e => e) (fun l r => l + r) (fun c t e _ => c + t + e)
      (.add (.lit 3) (.neg (.lit 4))) = 7 := by
  simp

example [Monad m] {σ : Type} (st : α → σ → σ) (f : α → Nat → σ → m Nat) (z : σ → m Nat) (s : σ) :
    MyList.accuM st z f (.cons a .nil) s
      = (do f a (← z (st a s)) s) := by
  simp

-- ── the fusion layer (slots 7, 9, 10): signatures and axiom checks ──

-- merge_accuM: banana split in the `Option` monad
example {α σ₁ σ₂ β₁ β₂ : Type}
    {st₁ : α → σ₁ → σ₁ × σ₁} {st₂ : α → σ₂ → σ₂ × σ₂}
    {z₁ : σ₁ → Option β₁} {z₂ : σ₂ → Option β₂}
    {f₁ : β₁ → α → β₁ → σ₁ → Option β₁} {f₂ : β₂ → α → β₂ → σ₂ → Option β₂}
    {s₁ : σ₁} {s₂ : σ₂} {r₁ : β₁} {r₂ : β₂} {t : MyTree α} :
    (MyTree.accuM st₁ z₁ f₁ t s₁ = some r₁ ∧ MyTree.accuM st₂ z₂ f₂ t s₂ = some r₂)
      ↔ MyTree.accuM
          (fun x p => (((st₁ x p.1).1, (st₂ x p.2).1), ((st₁ x p.1).2, (st₂ x p.2).2)))
          (fun p => z₁ p.1 >>= fun w₁ => z₂ p.2 >>= fun w₂ => pure (w₁, w₂))
          (fun v1 x v2 p =>
            f₁ v1.1 x v2.1 p.1 >>= fun w₁ => f₂ v1.2 x v2.2 p.2 >>= fun w₂ => pure (w₁, w₂))
          t (s₁, s₂) = some (r₁, r₂) :=
  MyTree.merge_accuM

-- fold_accu_Option_basic
example {β : Type} {v : β} {t : MyList α} {fn : β} {fc : α → β → β} :
    MyList.fold fn fc t = v ↔
    MyList.accuM (fun _ _ => ()) (fun _ => some fn) (fun a w _ => some (fc a w)) t () = some v :=
  MyList.fold_accu_Option_basic

-- s_unfold: the CorrectGen combinator the synthesizer applies
example {α β σ : Type} {st : α → σ → σ} {fn : σ → Option β} {fc : α → β → σ → Option β}
    {s : σ} {b : β}
    (g : (bg : β) → (sg : σ) → CorrectGen
      (fun (t : MyListF α β) =>
        (fn sg = some bg ∧ t = .nil) ∨ (∃ a w, fc a w sg = some bg ∧ t = .cons a w))) :
    CorrectGen (fun v => MyList.accuM st fn fc v s = some b) :=
  MyList.s_unfold g

/-- info: 'DeriveTest.Expr.merge_accuM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Expr.merge_accuM

/-- info: 'DeriveTest.Expr.fold_accu_Option_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Expr.fold_accu_Option_true

/-- info: 'DeriveTest.Expr.fold_accu_Option_function' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Expr.fold_accu_Option_function

/--
info: 'DeriveTest.Expr.fold_accu_Option_function_true' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Expr.fold_accu_Option_function_true

/--
info: 'DeriveTest.Expr.s_unfold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Expr.s_unfold

-- s_unfold_val is `rfl` and tagged @[extract], so extraction sees through `.val`
example {α β σ : Type} {st : α → σ → σ} {fn : σ → Option β} {fc : α → β → σ → Option β}
    {s : σ} {b : β} (g : (bg : β) → (sg : σ) → CorrectGen
      (fun (t : MyListF α β) =>
        (fn sg = some bg ∧ t = .nil) ∨ (∃ a w, fc a w sg = some bg ∧ t = .cons a w))) :
    (MyList.s_unfold (st_cons := st) (s := s) (b := b) g).val
      = MyList.unfold (fun _d p => (g p.1 p.2).val >>= fun tv =>
          match tv with
          | .nil => pure .nil
          | .cons a w => pure (.cons a (w, st a p.2))) (b, s) :=
  MyList.s_unfold_val g

-- ── universe-polymorphic inductives are instantiated at `Type` ──

inductive PolyList (α : Type u) where
  | pnil
  | pcons (x : α) (xs : PolyList α)

end DeriveTest

derive_palamedes DeriveTest.PolyList

namespace DeriveTest

example : {α β : Type} → β → (α → β → β) → PolyList α → β := @PolyList.fold

/-- info: 'DeriveTest.PolyList.support_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PolyList.support_unfold

-- ── unsupported shapes are rejected loudly ──

inductive Rose (α : Type) where
  | node (x : α) (kids : List (Rose α))

/-- error: derive_palamedes: nested inductives are not supported -/
#guard_msgs in
derive_palamedes Rose

end DeriveTest
