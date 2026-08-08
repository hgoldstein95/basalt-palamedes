/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Palamedes.Derive.Analyze
import Palamedes.Derive.BaseFunctor
import Palamedes.Derive.Recursion
import Palamedes.Derive.Fusion

/-!
# Boilerplate Automation for Recursive Structures

Given an inductive data type `X`, `derive_palamedes X` generates the whole per-datatype layer
required for Palamedes to generate values of that type. This includes: a base functor `XF`,
`X.fold`, the state-threading `X.accuM`, the `unfold` recursion scheme with its projection
equations, the support and totality lemmas, the fold/`accuM` fusion family, and the `CorrectGen`
combinator `X.s_unfold`.

The following are not supported: mutual, nested and indexed inductives, non-`Type` parameters, and
dependent constructor fields. Universe-polymorphic inductives (e.g. core `List`) are accepted and
instantiated at universe 0.

Debugging: `set_option trace.Palamedes.derive true` prints every generated command.
-/

open Lean Elab Command Meta
open Lean.Parser.Term (matchAltExpr matchAlt)
open Palamedes Palamedes.PGen Palamedes.PGen.Support

namespace Palamedes.Derive

syntax (name := derivePalamedes) "derive_palamedes " ident : command

@[command_elab derivePalamedes]
def elabDerivePalamedes : CommandElab := fun stx => do
  let xName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let ctx ← liftTermElabM do
    let ctx ← analyze xName
    genBaseFunctor xName ctx.fName
    pure ctx
  genFold ctx
  genAccuM ctx
  genUnfoldFamily ctx
  genUnfoldSupport ctx
  genSupportUnfold ctx SupportKit.spmf
  genSupportUnfold ctx SupportKit.optionT
  genSupportUnfoldCongr ctx
  genTotalUnfold ctx
  genTotalCases ctx
  genCoerceToFold ctx
  genMergeAccuM ctx
  genFoldAccuBasic ctx
  genFoldAccuTrue ctx
  genFoldAccuFunction ctx
  genFoldAccuFunctionTrue ctx
  genSUnfold ctx
  -- register the type with the synthesizer: `normalize_and_apply_unfold` reads this entry, so the
  -- derived type participates in unfold synthesis with no synthesizer edits. (Totality goes through
  -- the sibling registry — `genTotalUnfold` emits `total_unfold` with an `@[total]` tag.)
  liftCoreM <| Palamedes.registerUnfoldStrategy {
    typeName := ctx.xName
    sUnfold := ctx.name "s_unfold"
    fold := ctx.name "fold"
    coerce := ctx.name "coerce_to_fold"
    merge := ctx.name "merge_accuM"
    convert := #[ctx.name "fold_accu_Option_true", ctx.name "fold_accu_Option_function",
                 ctx.name "fold_accu_Option_function_true", ctx.name "fold_accu_Option_basic"]
    unfoldName := ctx.name "unfold"
  }

end Palamedes.Derive
