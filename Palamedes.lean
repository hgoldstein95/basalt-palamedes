/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

-- This module is the root of the `Palamedes` library: importing it brings the full public API into
-- scope — the `generator_search` tactic and `correct def` command (`Synthesizer`), the
-- `derive_palamedes` command that adds a datatype to the synthesizer (`Derive`), the supported
-- datatypes and their synthesis rules (`Data`), the `derive_tuning` command (`DeriveTuning`), the
-- runnable sampler (`Sample`), and the `#genstats` bridge (`Stats`). The example corpus and the
-- extraction audit live in the `PalamedesTest` library.
import Palamedes.Synthesizer
import Palamedes.Sample
import Palamedes.Stats
import Palamedes.Derive
import Palamedes.DeriveTuning
import Palamedes.Data
import Palamedes.Failure
