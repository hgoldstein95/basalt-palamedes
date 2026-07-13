import Palamedes.Derive
import Palamedes.Data.Stack.Atom

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
