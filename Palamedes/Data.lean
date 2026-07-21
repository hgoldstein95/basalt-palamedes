/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

-- Aggregator for the supported datatypes. The synthesis rules for each datatype are *registered by
-- its module* (an Aesop tag is only visible downstream of the module that declares it), so a user
-- who imports the library but not the right `Data` module gets a `generator_search` that silently
-- knows nothing about their primitives — `aesop made no progress` on a predicate the corpus
-- synthesizes fine. Importing this from the root makes `import Palamedes` mean what it says.
-- Corpus files keep importing individual modules: registration order affects rule order within an
-- Aesop probability tier, and the corpus is the oracle for that.
import Palamedes.Data.Bool
import Palamedes.Data.Color
import Palamedes.Data.List
import Palamedes.Data.Nat
import Palamedes.Data.Stack.Atom
import Palamedes.Data.Stack.Stack
import Palamedes.Data.STLC.Context
import Palamedes.Data.STLC.Term
import Palamedes.Data.STLC.Ty
import Palamedes.Data.Tree
import Palamedes.Data.Tuple
import Palamedes.Data.Unit
