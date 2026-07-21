import Palamedes.Synthesizer

open Palamedes Palamedes.PGen Palamedes.PGen.CorrectGen

namespace EvenLenAccuOpt

@[simp]
def isEvenLenAccuOpt (xs : List α) : Option Bool :=
  List.accuM
      (fun _ _ => ())
      (fun _ => some true)
      (fun _ b _ => some (!b))
      xs
      ()

/--
info: Try this:
  [apply] exact
    List.unfold
      (fun d p => do
        let tv ←
          if h : p.1 = true then
              PGen.oneOf
                [pure ListF.nil, do
                  let a ← arbNat
                  pure (ListF.cons a false)]
            else do
              let a ← arbNat
              pure (ListF.cons a true)
        match tv with
          | ListF.nil => pure ListF.nil
          | ListF.cons a1 a2 => pure (ListF.cons a1 (a2, PUnit.unit)))
      (true, PUnit.unit)
-/
#guard_msgs in
def genEvenLenAccuOpt : PGen (List Nat) := by
  generator_search? (fun xs => isEvenLenAccuOpt xs = some true)

end EvenLenAccuOpt
