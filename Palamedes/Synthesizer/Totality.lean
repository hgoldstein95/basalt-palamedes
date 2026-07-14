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
`apply` cascade is the structural reconstruction. `optimizeGen` has already eliminated every
satisfiable `assume`, so an `assume` reaching this tactic denotes a genuine filter and reconstruction
fails (the generator is partial; synthesize it with `allow_partial`).

Two things about the cascade below are not obvious:

* **The combinator basis is ordered.** `total_oneOf` must precede `total_frequency`: `oneOf` is
  definitionally a `frequency`, so the latter would capture the goal and leave a stuck
  `totalWeighted (List.map …)`. That is why the basis is hard-coded here rather than registered.
* **The per-datatype rules are not**, so they come from the `@[total]` registry, and a new datatype
  needs no edit to this file. Their goal shapes are pairwise disjoint, so at most one can ever apply.

`split`/`simp` at the end handle recursion: an `unfold` step is wrapped in a constructor `match`, and
`(casesOn a …).toGen = casesOn a (…toGen)` is not definitional — it needs `cases a`. -/
elab "totality" : tactic => open Lean Elab Tactic in do
  let leaves ← (Palamedes.totalLemmas (← getEnv)).mapM fun n =>
    `(tactic| apply $(mkIdent (`_root_ ++ n)):term)
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
        $[| $leaves:tactic]*
        | split
        | simp (config := {singlePass := true})))
