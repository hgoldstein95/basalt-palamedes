import Palamedes.Gen
import Palamedes.OptimizeCongr

namespace Palamedes

open Gen

theorem support_assume_pick :
    support (if h : b then pick (x h) y else y) = support (pick (assume b x) y) := by
  aesop

theorem support_pick_assume :
    support (if h : b then pick x (y h) else x) = support (pick x (assume b y)) := by
  aesop

theorem support_assume_bind :
    support (assume b (fun h => x h >>= f)) = support (assume b x >>= f) := by
  aesop

theorem support_pick_bind :
    support (pick (x >>= f) (y >>= f)) = support (pick x y >>= f) := by
  aesop

theorem support_if_bind
    {x : b = true → Gen α}
    {y : ¬ (b = true) → Gen α} :
    support (if h : b then x h >>= f else y h >>= f) = support ((if h : b then x h else y h) >>= f) := by
  aesop

theorem support_pure_bind :
    support (pure a >>= f) = support (f a) := by
  aesop

theorem support_bind_bind :
    support ((x >>= f) >>= g) = support (x >>= (fun a => f a >>= g)) := by
  aesop

@[gen_congr]
theorem support_bind_congr
    (hx : support x = support x')
    (hf : ∀ {a}, support (f a) = support (f' a)) :
    support (x >>= f) = support (x' >>= f') := by
  aesop

@[gen_congr]
theorem support_pick_congr
    (hx : support x = support x')
    (hy : support y = support y') :
    support (pick x y) = support (pick x' y') := by
  aesop

@[gen_congr]
theorem support_if_congr
    {P : Prop}
    [Decidable P]
    {x x' : P → Gen α}
    {y y' : ¬ P → Gen α}
    (hx : ∀ {h}, support (x h) = support (x' h))
    (hy : ∀ {h}, support (y h) = support (y' h)) :
    support (if h : P then x h else y h) = support (if h : P then x' h else y' h) := by
  aesop

/-- Non-dependent `if`-congruence. The dependent twin (`support_if_congr`) does not cover the plain
`ite` nodes the optimizer produces via `support_ite_bind`, so without this the optimizer could not
descend into `ite` branches. -/
@[gen_congr]
theorem support_ite_congr
    {P : Prop}
    [Decidable P]
    {x x' y y' : Gen α}
    (hx : support x = support x')
    (hy : support y = support y') :
    support (if P then x else y) = support (if P then x' else y') := by
  split <;> simp_all

@[gen_congr]
theorem support_assume_congr
    {f f' : b = true → Gen α}
    (hf : ∀ h, support (f h) = support (f' h)) :
    support (assume b f) = support (assume b f') := by
  aesop

theorem support_ite_bind
    {P : Prop} [Decidable P] {a b : Gen α} {f : α → Gen β} :
    support ((if P then a else b) >>= f) = support (if P then a >>= f else b >>= f) := by
  split <;> rfl

theorem support_bind_assume
    {x : Gen α} {b : Bool} {g : α → b = true → Gen β} :
    support (x >>= fun a => assume b (g a))
      = support (assume b fun h => x >>= fun a => g a h) := by
  aesop

theorem support_pick_assume_same
    {b : Bool} {f g : b = true → Gen α} :
    support (pick (assume b f) (assume b g))
      = support (assume b fun h => pick (f h) (g h)) := by
  aesop

/-- When the guard `b` holds, `assume b f` is its then-branch `f h`, with the dead `empty` else-branch
removed. The twin lemma for the optimizer's assume-discharge rewrite (`optimizeAssume?`); eliminating
the `empty` is what keeps a satisfiable-guarded generator `Fail`-free for the totality check. -/
theorem support_assume_true
    {b : Bool} {f : b → Gen α} (h : b = true) :
    support (assume b f) = support (f h) := by
  simp only [assume, dif_pos h]

theorem support_pick_flatten (x y : Gen α) :
    support (pick x y) = support (oneOf [x, y] (by simp)) := by
  aesop

theorem support_pick_flatten_left
    (x : Gen α) (xs : List (Gen α)) (hx : x :: xs ≠ []) (y : Gen α) :
    support (pick (oneOf (x :: xs) hx) y) = support (oneOf (x :: (xs ++ [y])) (by simp)) := by
  aesop

theorem support_pick_flatten_right
    (x y : Gen α) (ys : List (Gen α)) (hy : y :: ys ≠ []) :
    support (pick x (oneOf (y :: ys) hy)) = support (oneOf (x :: y :: ys) (by simp)) := by
  aesop

theorem support_pick_flatten_both
    (x : Gen α) (xs : List (Gen α)) (hx : x :: xs ≠ [])
    (y : Gen α) (ys : List (Gen α)) (hy : y :: ys ≠ []) :
    support (pick (oneOf (x :: xs) hx) (oneOf (y :: ys) hy))
      = support (oneOf (x :: (xs ++ y :: ys)) (by simp)) := by
  aesop

/-- Distribute a choice into a `dite`'s right arm: `pick x (dite c t f)` becomes
`dite c (pick x t) (pick x f)`. Composed with the flatten lemmas, this turns a choice nested under a
case split (`oneOf [x, dite c (oneOf [..]) ..]`) into a flat choice *inside* each branch — the shape
`installTuning` can address per constructor. Only the non-conditional arm `x` is duplicated; the
conditional arms `t`, `f` each stay in their one branch. -/
theorem support_pick_dite_right {α : Type} {P : Prop} [Decidable P]
    (x : Gen α) (t : P → Gen α) (f : ¬ P → Gen α) :
    support (pick x (if h : P then t h else f h))
      = support (if h : P then pick x (t h) else pick x (f h)) := by
  by_cases h : P <;> simp [h]

/-- Distribute a choice into a `dite`'s left arm. Mirror of `support_pick_dite_right`. -/
theorem support_pick_dite_left {α : Type} {P : Prop} [Decidable P]
    (y : Gen α) (t : P → Gen α) (f : ¬ P → Gen α) :
    support (pick (if h : P then t h else f h) y)
      = support (if h : P then pick (t h) y else pick (f h) y) := by
  by_cases h : P <;> simp [h]

theorem support_oneOf_congr {α : Type} {gs gs' : List (Gen α)}
    (hg : gs.map support = gs'.map support) (h : gs ≠ []) (h' : gs' ≠ []) :
    support (oneOf gs h) = support (oneOf gs' h') := by
  rw [Gen.Support.support_oneOf, Gen.Support.support_oneOf]
  funext a
  apply propext
  constructor
  · rintro ⟨g, hmem, ha⟩
    have hs : support g ∈ gs'.map support := by
      rw [← hg]; exact List.mem_map.mpr ⟨g, hmem, rfl⟩
    obtain ⟨g', hmem', he⟩ := List.mem_map.mp hs
    exact ⟨g', hmem', he ▸ ha⟩
  · rintro ⟨g, hmem, ha⟩
    have hs : support g ∈ gs.map support := by
      rw [hg]; exact List.mem_map.mpr ⟨g, hmem, rfl⟩
    obtain ⟨g', hmem', he⟩ := List.mem_map.mp hs
    exact ⟨g', hmem', he ▸ ha⟩

/-- `frequency`'s side-goal, which needs only the *first* weight to be positive (unlike
`support_oneOf_reweight` below, which needs all of them). -/
theorem sum_fst_pos_cons (α : Type) (w : Nat) (g : Gen α) (gs : List (Nat × Gen α)) (hw : 0 < w) :
    0 < (((w, g) :: gs).map Prod.fst).sum := by
  simp only [List.map_cons, List.sum_cons]
  omega

theorem allPos_nil (α : Type) : ∀ p ∈ ([] : List (Nat × Gen α)), 0 < p.1 := by simp

theorem allPos_cons (α : Type) (w : Nat) (g : Gen α) (gs : List (Nat × Gen α))
    (hw : 0 < w) (hgs : ∀ p ∈ gs, 0 < p.1) : ∀ p ∈ ((w, g) :: gs), 0 < p.1 := by
  intro p hp
  rcases List.mem_cons.mp hp with he | he
  · cases he; exact hw
  · exact hgs p he

/-- The correctness lemma for the optimizer's `installTuning` pass: installing all-positive weights
on a uniform `oneOf` preserves its support exactly, so `support = P` survives reweighting. -/
theorem support_oneOf_reweight (α : Type) (gs : List (Gen α)) (gs' : List (Nat × Gen α))
    (hsnd : gs'.map Prod.snd = gs) (hpos : ∀ p ∈ gs', 0 < p.1) (h) (h') :
    support (oneOf gs h) = support (frequency gs' h') := by
  subst hsnd
  rw [Gen.Support.support_oneOf, Gen.Support.support_frequency]
  funext a
  apply propext
  constructor
  · rintro ⟨g, hmem, ha⟩
    obtain ⟨⟨w, g'⟩, hmem', hg⟩ := List.mem_map.mp hmem
    cases hg
    exact ⟨w, g', hmem', hpos _ hmem', ha⟩
  · rintro ⟨w, g, hmem, _, ha⟩
    exact ⟨g, List.mem_map.mpr ⟨(w, g), hmem, rfl⟩, ha⟩

end Palamedes
