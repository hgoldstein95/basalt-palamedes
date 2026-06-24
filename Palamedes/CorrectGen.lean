import Palamedes.Gen
import Palamedes.Extract

namespace Palamedes

open Gen

/-- A generator bundled with a proof that its `support` (via the `SPMF` interpretation) equals the
target predicate `P`. This subtype is the object the deductive search actually constructs. -/
def CorrectGen (P : α → Prop) := {g : Gen α // g.support = P}

namespace Gen

namespace CorrectGen

def s_pure
    (a' : α) :
    CorrectGen (fun a => a = a') :=
  Subtype.mk (pure a') <| by
    simp

@[extract]
theorem s_pure_val
    (a' : α) :
    (s_pure a').val = pure a' := rfl

def s_bind
    {P : α → Prop}
    {Q : α → β → Prop}
    (x : CorrectGen P)
    (f : (a : α) → CorrectGen (Q a)) :
    CorrectGen (fun b => ∃ a, P a ∧ Q a b) :=
  Subtype.mk (x.val >>= fun a => (f a).val) <| by
    funext b
    simp
    apply Iff.intro <;>
      (intro ⟨a, ha⟩;
       exists a
       simp_all [x.property, (f a).property])

@[extract]
theorem s_bind_val
    {P : α → Prop}
    {Q : α → β → Prop}
    (x : CorrectGen P)
    (f : (a : α) → CorrectGen (Q a)) :
    (s_bind x f).val = x.val >>= fun a => (f a).val := rfl

def s_pick
    {P Q : α → Prop}
    (x : CorrectGen P)
    (y : CorrectGen Q) :
    CorrectGen (fun a => P a ∨ Q a) :=
  Subtype.mk (pick x.val y.val) <| by
    simp [x.property, y.property]

@[extract]
theorem s_pick_val
    {P Q : α → Prop}
    (x : CorrectGen P)
    (y : CorrectGen Q) :
    (s_pick x y).val = pick x.val y.val := rfl

def convert
    (h : P = Q)
    (g : CorrectGen P) :
    CorrectGen Q :=
  Subtype.mk g.val <| by
    simp [h, g.property]

@[extract]
theorem convert_val
    (h : P = Q)
    (g : CorrectGen P) :
    (convert h g).val = g.val := rfl

def duncurry
    {F : α × β → Type u} :
    ((a : α) → (b : β) → F (a, b)) → (p : α × β) → F p :=
  fun f p => f p.1 p.2

@[extract]
theorem duncurry_apply
    {F : α × β → Type u}
    (f : (a : α) → (b : β) → F (a, b))
    (p : α × β) :
    duncurry f p = f p.1 p.2 := rfl

/- Tactic-generated proof terms can wrap a `CorrectGen` in `id`, which blocks the `_val`
rewrites (e.g. `(id (convert h g)).val`). `id` is reducible, so the old delta-based
extraction removed it implicitly; the simp set must do so explicitly. -/
attribute [extract] id_eq

end CorrectGen

end Gen

end Palamedes
