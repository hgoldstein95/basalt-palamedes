import Palamedes.PGen
import Palamedes.OptimizeCongr

namespace Palamedes

open Palamedes.PGen

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
    {x : b = true → PGen α}
    {y : ¬ (b = true) → PGen α} :
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
    {x x' : P → PGen α}
    {y y' : ¬ P → PGen α}
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
    {x x' y y' : PGen α}
    (hx : support x = support x')
    (hy : support y = support y') :
    support (if P then x else y) = support (if P then x' else y') := by
  split <;> simp_all

@[gen_congr]
theorem support_assume_congr
    {f f' : b = true → PGen α}
    (hf : ∀ h, support (f h) = support (f' h)) :
    support (assume b f) = support (assume b f') := by
  aesop

theorem support_ite_bind
    {P : Prop} [Decidable P] {a b : PGen α} {f : α → PGen β} :
    support ((if P then a else b) >>= f) = support (if P then a >>= f else b >>= f) := by
  split <;> rfl

theorem support_bind_assume
    {x : PGen α} {b : Bool} {g : α → b = true → PGen β} :
    support (x >>= fun a => assume b (g a))
      = support (assume b fun h => x >>= fun a => g a h) := by
  aesop

theorem support_pick_assume_same
    {b : Bool} {f g : b = true → PGen α} :
    support (pick (assume b f) (assume b g))
      = support (assume b fun h => pick (f h) (g h)) := by
  aesop

/-- When the guard holds, `assume b f` is its then-branch, with the dead `empty` else-branch
removed. The twin lemma for the optimizer's assume-discharge rewrite (`optimizeAssume?`); eliminating
the `empty` is what keeps a satisfiable-guarded generator `Fail`-free for the totality check.

Stated at `b := true` rather than with a hypothesis `h : b = true`, and that is load-bearing for the
optimizer. `mkLeafProof` recovers a twin lemma's proof by unifying its *conclusion* against the goal,
so a hypothesis appearing only inside the right-hand side (as `h` did, in `support (f h)`) is not
determined by that unification and survives as an unassigned metavariable in the emitted proof. The
optimizer only fires this rewrite when the guard is definitionally `true`, so specializing costs
nothing and leaves the lemma hypothesis-free. -/
theorem support_assume_true
    {f : (true = true) → PGen α} :
    support (assume true f) = support (f rfl) := rfl

theorem support_pick_flatten (x y : PGen α) :
    support (pick x y) = support (oneOf [x, y] (by simp)) := by
  aesop

theorem support_pick_flatten_left
    (x : PGen α) (xs : List (PGen α)) (hx : x :: xs ≠ []) (y : PGen α) :
    support (pick (oneOf (x :: xs) hx) y) = support (oneOf (x :: (xs ++ [y])) (by simp)) := by
  aesop

theorem support_pick_flatten_right
    (x y : PGen α) (ys : List (PGen α)) (hy : y :: ys ≠ []) :
    support (pick x (oneOf (y :: ys) hy)) = support (oneOf (x :: y :: ys) (by simp)) := by
  aesop

theorem support_pick_flatten_both
    (x : PGen α) (xs : List (PGen α)) (hx : x :: xs ≠ [])
    (y : PGen α) (ys : List (PGen α)) (hy : y :: ys ≠ []) :
    support (pick (oneOf (x :: xs) hx) (oneOf (y :: ys) hy))
      = support (oneOf (x :: (xs ++ y :: ys)) (by simp)) := by
  aesop

/-- Distribute a choice into a `dite`'s right arm: `pick x (dite c t f)` becomes
`dite c (pick x t) (pick x f)`. Composed with the flatten lemmas, this turns a choice nested under a
case split (`oneOf [x, dite c (oneOf [..]) ..]`) into a flat choice *inside* each branch — the shape
`installTuning` can address per constructor. Only the non-conditional arm `x` is duplicated; the
conditional arms `t`, `f` each stay in their one branch. -/
theorem support_pick_dite_right {α : Type} {P : Prop} [Decidable P]
    (x : PGen α) (t : P → PGen α) (f : ¬ P → PGen α) :
    support (pick x (if h : P then t h else f h))
      = support (if h : P then pick x (t h) else pick x (f h)) := by
  by_cases h : P <;> simp [h]

/-- Distribute a choice into a `dite`'s left arm. Mirror of `support_pick_dite_right`. -/
theorem support_pick_dite_left {α : Type} {P : Prop} [Decidable P]
    (y : PGen α) (t : P → PGen α) (f : ¬ P → PGen α) :
    support (pick (if h : P then t h else f h) y)
      = support (if h : P then pick (t h) y else pick (f h) y) := by
  by_cases h : P <;> simp [h]

theorem support_oneOf_congr {α : Type} {gs gs' : List (PGen α)}
    (hg : gs.map support = gs'.map support) (h : gs ≠ []) (h' : gs' ≠ []) :
    support (oneOf gs h) = support (oneOf gs' h') := by
  rw [PGen.Support.support_oneOf, PGen.Support.support_oneOf]
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

/-- One direction of `support_frequency_congr`; the statement is symmetric in `gs`/`gs'`, so the
congruence applies this twice rather than duplicating the transport. -/
private theorem support_frequency_mem {α : Type} {gs gs' : List (Nat × PGen α)}
    (hg : gs.map (fun p => (p.1, support p.2)) = gs'.map (fun p => (p.1, support p.2))) {a : α}
    (hin : ∃ w g, (w, g) ∈ gs ∧ 0 < w ∧ support g a) :
    ∃ w g, (w, g) ∈ gs' ∧ 0 < w ∧ support g a := by
  obtain ⟨w, g, hmem, hw, ha⟩ := hin
  have hs : (w, support g) ∈ gs'.map (fun p => (p.1, support p.2)) := by
    rw [← hg]; exact List.mem_map.mpr ⟨(w, g), hmem, rfl⟩
  obtain ⟨⟨w', g'⟩, hmem', he⟩ := List.mem_map.mp hs
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, hsupp⟩ := he
  exact ⟨_, g', hmem', hw, by rw [hsupp]; exact ha⟩

/-- The `frequency` counterpart of `support_oneOf_congr`: rebuilding a `frequency` from optimized
branches preserves its support, provided every branch keeps its weight. This is what makes
`optimizeFrequencyChildren?` a real descent, so a hand-written `frequency` is visited rather than
silently skipped. -/
theorem support_frequency_congr {α : Type} {gs gs' : List (Nat × PGen α)}
    (hg : gs.map (fun p => (p.1, support p.2)) = gs'.map (fun p => (p.1, support p.2)))
    (h) (h') :
    support (frequency gs h) = support (frequency gs' h') := by
  rw [PGen.Support.support_frequency, PGen.Support.support_frequency]
  funext a
  exact propext ⟨fun hin => support_frequency_mem hg hin,
                 fun hin => support_frequency_mem hg.symm hin⟩

/-- `frequency`'s side-goal, which needs only the *first* weight to be positive (unlike
`support_oneOf_reweight` below, which needs all of them). -/
theorem sum_fst_pos_cons (α : Type) (w : Nat) (g : PGen α) (gs : List (Nat × PGen α)) (hw : 0 < w) :
    0 < (((w, g) :: gs).map Prod.fst).sum := by
  simp only [List.map_cons, List.sum_cons]
  omega

theorem allPos_nil (α : Type) : ∀ p ∈ ([] : List (Nat × PGen α)), 0 < p.1 := by simp

theorem allPos_cons (α : Type) (w : Nat) (g : PGen α) (gs : List (Nat × PGen α))
    (hw : 0 < w) (hgs : ∀ p ∈ gs, 0 < p.1) : ∀ p ∈ ((w, g) :: gs), 0 < p.1 := by
  intro p hp
  rcases List.mem_cons.mp hp with he | he
  · cases he; exact hw
  · exact hgs p he

/-- The correctness lemma for the optimizer's `installTuning` pass: installing all-positive weights
on a uniform `oneOf` preserves its support exactly, so `support = P` survives reweighting. -/
theorem support_oneOf_reweight (α : Type) (gs : List (PGen α)) (gs' : List (Nat × PGen α))
    (hsnd : gs'.map Prod.snd = gs) (hpos : ∀ p ∈ gs', 0 < p.1) (h) (h') :
    support (oneOf gs h) = support (frequency gs' h') := by
  subst hsnd
  rw [PGen.Support.support_oneOf, PGen.Support.support_frequency]
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
