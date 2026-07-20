import Palamedes.Synthesizer

open Palamedes Palamedes.Gen Palamedes.Gen.CorrectGen

namespace GoodStack

@[simp]
def isGoodNat (n : Nat) : Bool :=
  n == 0 || n == 1

@[simp]
def isGoodAtom : Atom → Bool
  | .atm n _ => isGoodNat n

@[simp]
def isGoodStack (s : Stack) (n : Nat) : Bool :=
  match s with
  | .mty => n == 0
  | .cons x s' => (n > 0 && isGoodAtom x) && isGoodStack s' (n - 1)
  | .ret_cons pc s' => (n > 0 && isGoodAtom pc) && isGoodStack s' (n - 1)

/--
info: Try this:
  [apply] exact
    Stack.unfold
      (fun d p => do
        let tv ←
          if p.2 = 0 then pure StackF.mty
            else
              Gen.oneOf
                [do
                  let a ←
                    Gen.oneOf
                        [do
                          let a ← arbLabel
                          pure (Atom.atm 0 a), do
                          let a ← arbLabel
                          pure (Atom.atm 1 a)]
                  pure (StackF.cons a PUnit.unit), do
                  let a ←
                    Gen.oneOf
                        [do
                          let a ← arbLabel
                          pure (Atom.atm 0 a), do
                          let a ← arbLabel
                          pure (Atom.atm 1 a)]
                  pure (StackF.ret_cons a PUnit.unit)]
        match tv with
          | StackF.mty => pure StackF.mty
          | StackF.cons a1 a2 => pure (StackF.cons a1 (a2, p.2 - 1))
          | StackF.ret_cons a1 a2 => pure (StackF.ret_cons a1 (a2, p.2 - 1)))
      (PUnit.unit, n)
-/
#guard_msgs in
def genGoodStack (n : Nat) : Gen Stack := by
  generator_search? (fun s => isGoodStack s n = true)

end GoodStack
