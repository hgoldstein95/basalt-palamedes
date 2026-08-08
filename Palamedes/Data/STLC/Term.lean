/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Derive
import Palamedes.Data.STLC.Ty

/-!
# The STLC `Term` datatype layer

STLC terms, `derive_palamedes`d, plus a hand-written fusion lemma (registered via
`unfold_strategy_convert`) and a `ToString` instance.
-/

section TypeDef

inductive Term : Type where
  | unit
  | var (n : Nat)
  | abs (τ : Ty) (t : Term)
  | app (t₁ t₂ : Term)
  deriving Repr

end TypeDef

derive_palamedes Term

section FoldConversions

theorem Term.fold_accu_Option_function_Option
    {α σ : Type}
    {i : σ}
    {v : α}
    {t : Term}
    {z : (σ → Option α)}
    {zn : Nat → (σ → Option α)}
    {f_abs : Ty → (σ → Option α) → (σ → Option α)}
    {f_app : (σ → Option α) → (σ → Option α) → (σ → Option α)}
    {g_abs : Ty → α → σ → Option α}
    {g_app : α → α → σ → Option α}
    {st_abs : Ty → σ → σ}
    {st_app₁ st_app₂ : σ → σ}
    (h_abs : ∀ τ acc s w,
      f_abs τ acc s = some w ↔ (do g_abs τ (← acc (st_abs τ s)) s) = some w)
    (h_app : ∀ acc₁ acc₂ s w,
      f_app acc₁ acc₂ s = some w ↔
        (do g_app (← acc₁ (st_app₁ s)) (← acc₂ (st_app₂ s)) s) = some w)
    :
    Term.fold z zn f_abs f_app t i = some v ↔
    Term.accuM
      st_abs
      (fun s => (st_app₁ s, st_app₂ s))
      (fun s => z s)
      (fun n s => zn n s)
      g_abs
      g_app
      t
      i = some v := by
  induction t generalizing i v <;> simp_all [Term.fold, Term.accuM, Option.bind_eq_some_iff]

end FoldConversions

unfold_strategy_convert Term Term.fold_accu_Option_function_Option

namespace PrettyPrint

def Term.toString : Term → String
  | .unit => "()"
  | .var n => s!"(var {n})"
  | .abs τ t => s!"({Ty.toString τ} → {Term.toString t})"
  | .app t₁ t₂ => s!"({Term.toString t₁} {Term.toString t₂})"

instance : ToString Term where
  toString := Term.toString

end PrettyPrint
