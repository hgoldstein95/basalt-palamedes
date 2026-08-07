/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Harrison Goldstein, Hila Peleg, Cassia Torczon,
  Leonidas Lampropoulos, Benjamin C. Pierce
-/

-- This module is the root of the `Palamedes` library: importing it brings the full public API into
-- scope — the `generator_search` tactic and `@[correct]` attribute (`Synthesizer`), the
-- `derive_palamedes` command that adds a datatype to the synthesizer (`Derive`), the supported
-- datatypes and their synthesis rules (`Data`), and the retry loop a filtering generator samples
-- through (`Sample`). A synthesized generator is a Basalt generator, so Basalt's own `#genstats`
-- consumes it with no bridge on this side. Weighting is part of synthesis rather than a separate
-- command: a `Tuning` binder in a generator's signature is threaded through its choice sites
-- (`Tuning`), and the depth-decaying schedules that populate one live in `Schedule`. The example
-- corpus and the extraction audit live in the `PalamedesTest` library.
import Palamedes.Synthesizer
import Palamedes.Sample
import Palamedes.Derive
import Palamedes.Schedule
import Palamedes.Data
import Palamedes.Failure
