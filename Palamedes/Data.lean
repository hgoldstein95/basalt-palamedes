/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

import Palamedes.Data.Bool
import Palamedes.Data.Color
import Palamedes.Data.List
import Palamedes.Data.List.Elements
import Palamedes.Data.Nat
import Palamedes.Data.Stack.Atom
import Palamedes.Data.Stack.Stack
import Palamedes.Data.STLC.Term
import Palamedes.Data.STLC.Ty
import Palamedes.Data.Tree
import Palamedes.Data.Tuple
import Palamedes.Data.Unit

/-!
# Aggregator for Supported Datatypes

These modules contain the built-in datatypes that Palamedes supports. Each of these modules tags
lemmas and synthesis rules for Aesop, which it can then use as part of the synthesis process.
If you want to work with your own data type, see the `derive_palamedes` command.
-/
