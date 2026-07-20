import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace SortedBetween

@[simp]
def isSortedBetween (xs : List Nat) : Nat × Nat → Bool := fun (lo, hi) =>
  match xs with
  | [] => true
  | x :: xs' => (lo <= x && x <= hi) && isSortedBetween xs' (x, hi)

/--
info: Try this:
  [apply] exact
    List.unfold
      (fun d p => do
        let tv ←
          if h : decide (p.2.1 ≤ p.2.2) = true then
              Gen.oneOf
                [pure ListF.nil, do
                  let a ← choose p.2.1 p.2.2
                  pure (ListF.cons a PUnit.unit)]
            else pure ListF.nil
        match tv with
          | ListF.nil => pure ListF.nil
          | ListF.cons a1 a2 => pure (ListF.cons a1 (a2, a1, p.2.2)))
      (PUnit.unit, lo, hi)
-/
#guard_msgs in
def genSortedBetween (lo hi : Nat) : Gen (List Nat) := by
  generator_search? (fun xs => isSortedBetween xs (lo, hi) = true)

end SortedBetween
