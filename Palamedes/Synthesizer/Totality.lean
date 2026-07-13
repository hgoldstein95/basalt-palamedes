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
`@[simp]` `total_*` lemmas.

The per-datatype `total_unfold` steps are read from the `unfold_strategy` registry (see
`Palamedes.UnfoldStrategy`), which `derive_palamedes` populates. -/
elab "totality" : tactic => open Lean Elab Tactic in do
  let entries := Palamedes.unfoldStrategies (← getEnv)
  let alts ← entries.mapM fun e => do
    let tu : Lean.Term := mkIdent (`_root_ ++ e.totalUnfold)
    `(tactic| apply $tu:term)
  evalTactic (← `(tactic|
    repeat'
      first
        | (intro)
        | apply total_pure
        | apply total_bind
        | apply total_pick
        | apply total_oneOf
        | apply total_frequency
        | apply totalList_cons
        | apply totalList_nil
        | apply totalWeighted_cons
        | apply totalWeighted_nil
        | apply total_map
        | apply total_dite
        | apply total_arbBool
        | apply total_Bool_rec
        | apply total_arbColor
        | apply total_arbNat
        | apply total_choose
        | apply total_gt
        | apply total_lt
        | apply total_arbLabel
        | apply total_elements
        | apply total_arbTy
        | apply total_Ty_caseTy
        $[| $alts:tactic]*
        | split
        | simp (config := {singlePass := true})))
