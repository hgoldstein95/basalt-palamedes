/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Derive

derive_palamedes List

section FoldConversions

theorem List.fold_accu_cond
  {α σ : Type}
  {i : σ}
  {stTrue stFalse : α -> σ -> σ}
  {condTrue condFalse initCond : σ -> Bool}
  {xs : List α}
  {condGuard : α -> σ -> Bool} :
  List.fold
    (fun s => initCond s)
    (fun x acc s => if condGuard x s = true then
                      condTrue s && acc (stTrue x s) else
                      condFalse s && acc (stFalse x s))
    xs
    i = true ↔
  List.accuM
    (fun x s => if condGuard x s then stTrue x s else stFalse x s)
    (fun s => guard $ initCond s)
    (fun x _ s =>
      if condGuard x s then guard $ condTrue s else guard $ condFalse s)
    (xs : List α)
    i = some () := by
  induction xs generalizing i <;> simp_all [List.fold, List.accuM, Option.bind_eq_some_iff, guard]
  case cons head tail ih =>
    cases (condGuard head i) <;> aesop

end FoldConversions

unfold_strategy_cond List List.fold_accu_cond
