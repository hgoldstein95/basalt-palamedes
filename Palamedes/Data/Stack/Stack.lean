/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Derive
import Palamedes.Data.Stack.Atom

/-!
# The `Stack` datatype layer

The IFC machine stack (adapted from QuickChick's ifc-basic example), `derive_palamedes`d, plus a
`ToString` instance.
-/

section TypeDef
/- adapted from https://github.com/QuickChick/QuickChick/tree/master/examples/ifc-basic -/

inductive Stack where
  | mty
  | cons (a : Atom) (s : Stack)
  | ret_cons (pc : Atom) (s : Stack)

end TypeDef

derive_palamedes Stack

namespace PrettyPrint

def Stack.toString : Stack → String
  | .mty => "(empty)"
  | .cons a s  => s!"(cons {Atom.toString a} {Stack.toString s})"
  | .ret_cons pc s => s!"(ret_cons {Atom.toString pc} {Stack.toString s})"

instance : ToString Stack where
  toString := Stack.toString

end PrettyPrint
