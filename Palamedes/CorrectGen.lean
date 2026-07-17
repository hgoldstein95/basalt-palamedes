import Palamedes.Gen
import Palamedes.Extract

namespace Palamedes

open Gen

/-- A generator bundled with a proof that its `support` (via the `SPMF` interpretation) equals the
target predicate `P`. This subtype is the object the deductive search actually constructs. -/
def CorrectGen (P : α → Prop) := {g : Gen α // g.support = P}

namespace Gen

namespace CorrectGen

@[extract]
def s_pure
    (a' : α) :
    CorrectGen (fun a => a = a') :=
  Subtype.mk (pure a') <| by
    simp

@[extract]
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
def s_pick
    {P Q : α → Prop}
    (x : CorrectGen P)
    (y : CorrectGen Q) :
    CorrectGen (fun a => P a ∨ Q a) :=
  Subtype.mk (pick x.val y.val) <| by
    simp [x.property, y.property]

@[extract]
def convert
    (h : P = Q)
    (g : CorrectGen P) :
    CorrectGen Q :=
  Subtype.mk g.val <| by
    simp [h, g.property]

@[extract]
def duncurry
    {F : α × β → Type u} :
    ((a : α) → (b : β) → F (a, b)) → (p : α × β) → F p :=
  fun f p => f p.1 p.2

/- Tactic-generated proof terms can wrap a `CorrectGen` in `id`, which blocks the `_val`
rewrites (e.g. `(id (convert h g)).val`). `id` is reducible, but the `extract` simp set must
remove it explicitly. -/
attribute [extract] id_eq

end CorrectGen

end Gen

end Palamedes
