import Palamedes.Data.List
import Palamedes.Data.Stack.Stack
import Palamedes.Data.STLC.Ty
import Palamedes.Data.STLC.Term
import Palamedes.Data.Tree
import Palamedes.Data.Nat
import Palamedes.Total

open Palamedes Palamedes.Gen Palamedes.Gen.Total

/-- Prove `Gen.total g` by reconstructing a `TGen` (`Fail`-free) witness over `g`'s combinator spine.

Each `total_*` lemma maps one `Gen` combinator to its `TGen` twin and closes by `ext; rfl`, so the
`apply` cascade is the structural reconstruction. `optimizeGen` has already eliminated every satisfiable
`assume`, so an `assume` reaching this tactic denotes a genuine filter and reconstruction fails (the
generator is partial; synthesize it with `allow_partial`).

`split`/`simp` handle recursion: a per-datatype `unfold` step is wrapped in a constructor `match`
(`ListF.casesOn …`), and `(casesOn a …).toGen = casesOn a (…toGen)` is not definitional — it needs
`cases a`. `split` performs that case analysis and `simp` discharges the resulting leaves via the
`@[simp]` `total_*` lemmas. -/
macro "totality" : tactic =>
  `(tactic|
    repeat'
      first
        | (intro)
        | apply total_pure
        | apply total_bind
        | apply total_pick
        | apply total_map
        | apply total_dite
        | apply total_arbBool
        | apply total_Bool_rec
        | apply total_arbColor
        | apply total_arbNat
        | apply total_choose
        | apply total_gt
        | apply total_lt
        | apply Tree.total_unfold
        | apply Stack.total_unfold
        | apply total_arbLabel
        | apply total_elements
        | apply total_arbTy
        | apply total_Ty_caseTy
        | apply Term.total_unfold
        | apply List.total_unfold
        | split
        | simp (config := {singlePass := true}))
