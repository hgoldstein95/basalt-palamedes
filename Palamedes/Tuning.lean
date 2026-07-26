/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.GenTransform
import Palamedes.Schedule

/-!
# Threading a runtime `Tuning` through a synthesized generator

A generator's branch weights live in its choice sites. `installTuning` rewrites each uniform
`PGen.oneOf` into a `PGen.frequency` whose weights read a runtime `θ : Tuning`
(`Tuning.weight θ (offset+j) d`), so a different weighting is a function call away instead of an
edit-and-recompile away. The affine schedules that populate a `θ` live in `Palamedes.Schedule`;
`Tuning`, `Site` and `Tuning.weight` are **Basalt's**, so a tuned Palamedes generator speaks the
same vocabulary as a hand-written `tunable def` and picks up whatever Basalt's tuning layer grows
next.

## Why this is a pipeline stage and not a command

It used to be `derive_tuning genFoo`, run *after* the declaration existed. That ordering is what
made it expensive. The rewrite substrate is the `Palamedes.PGen` carrier — `installTuning` keys on
`PGen.oneOf`, and the optimizer's `support lhs = support rhs` chaining does not typecheck at an
abstract `G` — so a Basalt-shaped declaration could not be rewritten in place. It had to be tuned
through a *carrier companion* and then re-projected: re-run the `totality` cascade on the θ-open
term, re-derive the `someSupport` bridge, extract a second witness, and finally check that the
result was still a tuning *of the original declaration* at all, since the companion was located by
name and nothing else related the two generators.

Running the pass **inside** the pipeline, between optimize and totality, deletes all of that. There
is one generator, tuned before it is ever packaged; stage 4 builds its witness once; and the law
`@[correct]` emits is θ-generalized for free, because `θ` is one of the declaration's own binders
rather than a parameter invented after the fact.

`θ` is exactly that — a binder the user wrote:

```lean4
def genTree (θ : Tuning := .uniform) [Gen G] : G (Tree Nat) := by generator_search isBalanced
```

`generator_search` threads whatever `Tuning`-typed binder is in scope, and skips this pass when
there is none — so opting out is spelling the signature without one. `.uniform` is a universal
default: `Tuning.weight` reads `θ.schedules.getD i (1, 0)`, so the empty tuning is the uniform
weighting of *any* generator, with no site table needed. That is what lets the ordinary call
`genTree` mention tuning nowhere.
-/

open Lean Meta

/-- The uniform weighting, for any generator at all.

`Tuning.weight` falls back to `(1, 0)` for an index the schedule array does not reach, so the empty
tuning weights every branch of every site equally without having to know how many there are. This is
what makes `(θ : Tuning := .uniform)` a signature a user can write before knowing the site count. -/
def Tuning.uniform : Tuning := ⟨#[]⟩

namespace Palamedes

/-- A `frequency` site; the internal form of Basalt's `Site`. `offset` is the site's first index into
the flat `Tuning.schedules` array. -/
structure TuningSiteInfo where
  name : Name
  offset : Nat
  arity : Nat
  holes : Array Nat
  deriving Inhabited

/-- The `installTuning` pass's threaded state: the next free offset and the sites collected so far,
in assignment order. -/
structure TuningState where
  nextOffset : Nat := 0
  sites : Array TuningSiteInfo := #[]
  deriving Inhabited

private def mkTunedWeight (θ : Expr) (idx : Nat) (depth : Expr) : MetaM Expr :=
  mkAppM ``Tuning.weight #[θ, mkNatLit idx, depth]

private def mkTunedWeightPos (θ : Expr) (idx : Nat) (depth : Expr) : MetaM Expr :=
  mkAppM ``Tuning.weight_pos #[θ, mkNatLit idx, depth]

/-- `∀ p ∈ gs', 0 < p.1` for a `θ`-weighted branch list, folded from `Tuning.weight_pos` at each
branch's flat index. -/
private def mkAllPosTuning (α θ : Expr) (pairs : List (Expr × Expr)) (idxs : List Nat)
    (depth : Expr) : MetaM Expr := do
  match pairs, idxs with
  | [], _ => mkAppM ``allPos_nil #[α]
  | (w, g) :: ps, i :: is =>
    let tl ← mkListLit (← mkAppM ``Prod #[mkConst ``Nat, ← mkAppM ``PGen #[α]])
      (← ps.mapM fun (w, g) => mkAppM ``Prod.mk #[w, g])
    let hw ← mkTunedWeightPos θ i depth
    mkAppM ``allPos_cons #[α, w, g, tl, hw, ← mkAllPosTuning α θ ps is depth]
  | _, _ => throwError "installTuning: branch/index length mismatch"

/-- The head rewrite: a uniform `oneOf` becomes a `frequency` weighted by `Tuning.weight θ (offset+j)
d`, appending a `TuningSiteInfo`. Children rewrite before their parent, so offsets run innermost-first
— consistent because the one pass both assigns and records them. -/
private def installTuning? (θ : Expr) (st : IO.Ref TuningState) (declName : Name)
    (depth? : Depth) (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match_expr e with
  | PGen.oneOf α gs h => do
    let some elems := listLitElems? gs | return none
    if elems.isEmpty then return none
    -- depth expr (or `0` outside a recursion) and per-branch recursive-child counts
    let (depth, holes) ← match depth? with
      | some (d, typeName) => do
          let hm ← baseCtorHoles (typeName.appendAfter "F")
          let hs ← elems.mapM (branchHoles hm)
          pure (d, hs.toArray)
      | none => pure (mkNatLit 0, Array.replicate elems.length 0)
    let cur ← st.get
    let offset := cur.nextOffset
    let arity := elems.length
    let siteName := declName ++ Name.mkSimple s!"site{cur.sites.size}"
    let idxs := (List.range arity).map (offset + ·)
    let ws ← idxs.mapM (mkTunedWeight θ · depth)
    let pairs := ws.zip elems
    let pairExprs ← pairs.mapM fun (w, g) => mkAppM ``Prod.mk #[w, g]
    let prodTy ← mkAppM ``Prod #[mkConst ``Nat, ← mkAppM ``PGen #[α]]
    let gs' ← mkListLit prodTy pairExprs
    -- the `frequency` side-goal `0 < Σ wⱼ(d)`, from the first weight's positivity alone
    let hw0 ← mkTunedWeightPos θ offset depth
    let tl ← mkListLit prodTy pairExprs.tail!
    let h' ← mkAppM ``sum_fst_pos_cons #[α, ws.head!, elems.head!, tl, hw0]
    let e' ← mkAppM ``PGen.frequency #[gs', h']
    let hpos ← mkAllPosTuning α θ pairs idxs depth
    let hsnd ← mkEqRefl gs
    let proof ← mkAppM ``support_oneOf_reweight #[α, gs, gs', hsnd, hpos, h, h']
    st.set { nextOffset := offset + arity, sites := cur.sites.push ⟨siteName, offset, arity, holes⟩ }
    return some (e', proof)
  | _ => return none

/-- What `installTuning` produced. -/
structure TuningResult where
  /-- The θ-threaded generator: every `oneOf` is now a `frequency` reading `θ`. -/
  gen : Expr
  /-- The `frequency` sites, in offset-assignment order. -/
  sites : Array TuningSiteInfo
  /-- `support original = support gen` — the same orientation `transform` and `optimizeGen` use, so
  the pipeline chains it exactly like an optimizer pass. `none` when no site fired, i.e. the term is
  unchanged and the equation is `rfl`. -/
  supportProof? : Option Expr

/-- Thread `θ` through a generator term, producing the tuned term and its site table.

The recursion is the `unfold` combinator, not an `Order.fix`, so it is left untouched — there is no
monotonicity proof to rebuild. `installTuning` proves support-preservation per site
(`support_oneOf_reweight`, parametric in `θ`) and the traversal chains them. That is what makes a
`Tuning` able to change a generator's *distribution* and never its support, whatever weights a
policy proposes. -/
def installTuning (declName : Name) (θ gen : Expr) : MetaM TuningResult := do
  let table := getGenCongrRules (← getEnv)
  let st ← IO.mkRef ({} : TuningState)
  let r ← transform (fun depth e => installTuning? θ st declName depth e) table none gen
  return { gen := r.expr, sites := (← st.get).sites, supportProof? := r.proof? }

/-- The site table as a Basalt `Array Site` literal, for `addDecl`ing as `genFoo.sites`.

This is closed data — it does not mention the generator — which is why the *tactic* can emit it
while the declaration it belongs to is still being elaborated. Only theorems *about* the constant
have to wait for `@[correct]`. -/
def mkSitesValue (sites : Array TuningSiteInfo) : MetaM Expr := do
  let siteExprs ← sites.toList.mapM fun s => pure <|
    mkAppN (mkConst ``Site.mk) #[toExpr s.name, toExpr s.offset, toExpr s.arity, toExpr s.holes]
  mkAppM ``List.toArray #[← mkListLit (mkConst ``Site) siteExprs]

end Palamedes
