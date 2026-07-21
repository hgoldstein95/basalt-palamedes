/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Derive

-- Lean core (v4.32+) declares a deprecated `Tree` (alias for `BinaryTree`) at the root namespace, so
-- Palamedes' own `Tree` lives under `namespace Palamedes` to avoid the clash.
namespace Palamedes

section TypeDef

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : (l : Tree α) → (x : α) → (r : Tree α) → Tree α
deriving Repr

end TypeDef

end Palamedes

derive_palamedes Palamedes.Tree

namespace Palamedes

section FoldConversions

theorem Tree.fold_accu_cond
  {α σ : Type}
  {i : σ}
  {stTrue stFalse : α -> σ -> σ}
  {condTrue condFalse initCond : σ -> Bool}
  {t : Tree α}
  {condGuard : α -> σ -> Bool} :
  Tree.fold
    (fun s => initCond s)
    (fun accL x accR s => if condGuard x s then
                      condTrue s && accL (stTrue x s) && accR (stTrue x s) else
                      condFalse s && accL (stFalse x s) && accR (stFalse x s))
    t
    i = true ↔
  Tree.accuM
    (fun x s => if condGuard x s then (stTrue x s, stTrue x s) else (stFalse x s, stFalse x s))
    (fun s => guard $ initCond s)
    (fun _ x _ s =>
      if condGuard x s then guard $ condTrue s else guard $ condFalse s)
    t
    i = some () := by
    induction t generalizing i <;> simp_all [Tree.fold, Tree.accuM, Option.bind_eq_some_iff, guard]
    case node l v r ihl ihr =>
      cases (condGuard v i) <;> aesop

end FoldConversions

unfold_strategy_cond Tree Tree.fold_accu_cond

namespace PrettyPrint

def Tree.toString [ToString α] : Tree α → String
  | .leaf => "(leaf)"
  | .node l x r => s!"(node {Tree.toString l} {x} {Tree.toString r})"

instance [ToString α] : ToString (Tree α) where
  toString := Tree.toString

end PrettyPrint

end Palamedes
