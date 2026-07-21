import Lean
import Palamedes.Optimizer

open Lean Elab Command Term Meta Palamedes Palamedes.PGen

syntax (name := assertOptimizes) "#assert_optimizes! " term " goes_to " term : command

@[command_elab assertOptimizes]
def expandAssertOptimizes : CommandElab := fun stx =>
  match stx with
  | `(#assert_optimizes! $t1:term goes_to $t2:term) => do
    liftTermElabM do
      let mα ← mkFreshExprMVar none
      let e1 ← elabTerm t1 (some (.app (.const ``Palamedes.PGen []) mα))
      let e2 ← elabTerm t2 (some (.app (.const ``Palamedes.PGen []) mα))
      let (e1', proof) ← Palamedes.optimizeGen e1
      unless ← isDefEq e1' e2 do
        throwError "{e1}\n~~>\n{e1'}\n!=\n{e2}"

      -- The optimizer now hands back a proof that `support` was preserved; check it proves exactly
      -- `support e1 = support e1'` and is well-typed.
      let thm ← mkEq (← mkAppM ``Palamedes.PGen.support #[e1]) (← mkAppM ``Palamedes.PGen.support #[e1'])
      unless ← isDefEq (← inferType proof) thm do
        throwError "carried proof has wrong type: expected {thm}, got {← inferType proof}"
      try
        Lean.Meta.check proof
      catch e =>
        throwError "carried proof does not type-check\n{e.toMessageData}"
  | _ => throwError "invalid syntax {stx}"

private axiom g : PGen Nat
private axiom f : Nat → PGen Nat

#assert_optimizes!
  (pure 5 : PGen Nat) >>= fun x => pure (x + 1)
  goes_to
  (fun x => pure (x + 1)) 5

#assert_optimizes!
  (g >>= fun x => pure (x + 1)) >>= fun x => pure (x + 2)
  goes_to
  g >>= (fun x => pure ((x + 1) + 2))

#assert_optimizes!
  pick (assume ((2 : Nat) == 2) (fun _ => (pure 3 : PGen Nat))) (pure 4)
  goes_to
  if _ : (2 == 2) then oneOf [pure 3, pure 4] else pure 4

-- TODO: Can we do better? Ideally we could apply a heuristic here to try to figure out which one is
-- easier to satisfy...
#assert_optimizes!
  pick (assume ((2 : Nat) == 2) (fun _ => (pure 2 : PGen Nat))) (assume ((3 : Nat) == 3) (fun _ => pure 3))
  goes_to
  if _ : ((2 : Nat) == 2) then oneOf [pure 2, pure 3] else pure 3

#assert_optimizes!
  (assume ((2 : Nat) == 2) (fun _ => pure 3)) >>= f
  goes_to
  assume ((2 : Nat) == 2) (fun _ => f 3)

#assert_optimizes!
  g >>= (fun x => assume ((2 : Nat) == 2) (fun _ => pure (x + 1)))
  goes_to
  assume ((2 : Nat) == 2) (fun h => g >>= fun x => (fun _ => pure (x + 1)) h)

#assert_optimizes!
  pick (pure 4 : PGen Nat) (assume ((2 : Nat) == 2) (fun _ => pure 3))
  goes_to
  if _ : ((2 : Nat) == 2) then oneOf [pure 4, pure 3] else pure 4

#assert_optimizes!
  pick (pure 1) (pick (pure 2) (pick (pure 3 : PGen Nat) (pure 4)))
  goes_to
  oneOf [pure 1, pure 2, pure 3, pure 4]

#assert_optimizes!
  pick (pick (pick (pure 1 : PGen Nat) (pure 2)) (pure 3)) (pure 4)
  goes_to
  oneOf [pure 1, pure 2, pure 3, pure 4]

#assert_optimizes!
  pick (pick (pure 1 : PGen Nat) (pure 2)) (pick (pure 3) (pure 4))
  goes_to
  oneOf [pure 1, pure 2, pure 3, pure 4]

-- A lone binary choice also lands in `oneOf`: the distribution is unchanged (uniform either way),
-- and every choice point ends up in the one node kind that weights can attach to.
#assert_optimizes!
  pick (pure 1 : PGen Nat) (pure 2)
  goes_to
  oneOf [pure 1, pure 2]

-- The optimizer descends into a `oneOf`'s branches (`optimizeOneOfChildren?`, a bespoke descent —
-- the `@[gen_congr]` table cannot rebuild a `oneOf`). `#assert_optimizes!` also type-checks the
-- carried support proof, so a mis-built congruence term fails here rather than silently skewing a
-- distribution.
#assert_optimizes!
  oneOf [(pure 5 : PGen Nat) >>= fun x => pure (x + 1), pure 2]
  goes_to
  oneOf [(fun x => pure (x + 1)) 5, pure 2]

-- ...and recursively: a choice nested in another choice's branch is reachable. It used to be that
-- `installTuning` could not see the inner `oneOf` at all.
#assert_optimizes!
  oneOf [oneOf [(pure 5 : PGen Nat) >>= fun x => pure (x + 1), pure 2], pure 3]
  goes_to
  oneOf [oneOf [(fun x => pure (x + 1)) 5, pure 2], pure 3]

-- The same for a hand-written `frequency` (`optimizeFrequencyChildren?`). Until this existed,
-- `frequency` was exempted from the descent guard by name: a `frequency` in a *reducible* position
-- had its branches silently skipped, and the exemption's comment carried the gap as a known risk.
-- Weights must survive the rebuild untouched — only the generators are optimized.
#assert_optimizes!
  frequency [(2, (pure 5 : PGen Nat) >>= fun x => pure (x + 1)), (1, pure 2)]
  goes_to
  frequency [(2, (fun x => pure (x + 1)) 5), (1, pure 2)]

-- ...and nested, which is the case `installTuning` needs: a choice under a hand-written `frequency`
-- is now reached and rewritten rather than passed over.
#assert_optimizes!
  frequency [(3, oneOf [(pure 5 : PGen Nat) >>= fun x => pure (x + 1), pure 2]), (1, pure 3)]
  goes_to
  frequency [(3, oneOf [(fun x => pure (x + 1)) 5, pure 2]), (1, pure 3)]
