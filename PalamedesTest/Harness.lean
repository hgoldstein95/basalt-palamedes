/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein
-/

import Lean

/-!
# Scaffolding shared by the audit modules

An environment-walking audit needs a walk that fails when it matched nothing, and a way to assert
that a companion declaration was deliberately *not* emitted.
-/

open Lean Elab Command

namespace PalamedesTest

/-- Visit every constant declared in an imported module `inScope` accepts, counting those `visit`
reports as audited, and fail with `emptyMsg` when that count is zero: an audit whose walk matched
nothing passes for the same reason a clean one does. -/
def auditConstants (inScope : Name → Bool) (emptyMsg : MessageData)
    (visit : Name → TermElabM Bool) : TermElabM Unit := do
  let env ← getEnv
  let mut total := 0
  for i in [0:env.header.moduleData.size] do
    unless inScope env.header.moduleNames[i]! do continue
    for n in env.header.moduleData[i]!.constNames do
      if ← visit n then total := total + 1
  if total == 0 then logError emptyMsg

/-- Fail the build if `name` was declared; `why` says what its absence means. -/
def assertNotDeclared (name : Name) (why : MessageData) : CommandElabM Unit := do
  if (← getEnv).contains name then
    throwError "`{name}` was declared, but {why}"

end PalamedesTest
