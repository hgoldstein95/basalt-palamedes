-- This module is the root of the `Palamedes` library: importing it brings the full public API into
-- scope — the `generator_search` tactic (`Synthesizer`), the `derive_palamedes` command that adds a
-- datatype to the synthesizer (`Derive`), the runnable sampler (`Sample`), and the `#genstats`
-- bridge (`Stats`). The example corpus and the extraction audit live in the `PalamedesTest` library.
import Palamedes.Synthesizer
import Palamedes.Sample
import Palamedes.Stats
import Palamedes.Derive
