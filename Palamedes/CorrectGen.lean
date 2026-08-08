/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.PGen
import Palamedes.Extract

/-!
# Correct generators

`CorrectGen P` is a generator bundled with a proof that its support is exactly `P` — the object the
deductive search constructs; synthesis is a proof search for an inhabitant. The `s_*` definitions
here are the core combinators that search composes, each tagged `@[extract]` so the raw `PGen` can
be projected back out afterwards.
-/

namespace Palamedes

open Palamedes.PGen

/-- A generator bundled with a proof that its `support` (via the `SPMF` interpretation) equals the
target predicate `P`.

`implicit_reducible` is load-bearing: unfolding an `@[extract]` combinator leaves a subterm typed at
bare `Subtype …` where `CorrectGen …` is expected. Since Lean 4.33 metavariable assignment compares
types at `implicit` transparency, so a semireducible `CorrectGen` makes those rewrites silently stop
firing (see `PalamedesTest/Extract.lean`). -/
@[implicit_reducible]
def CorrectGen (P : α → Prop) := {g : PGen α // g.support = P}

namespace PGen

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

/- Tactic-generated proof terms can wrap a `CorrectGen` in `id`, which blocks the `_val` rewrites
(e.g. `(id (convert h g)).val`). -/
attribute [extract] id_eq

end CorrectGen

end PGen

end Palamedes
