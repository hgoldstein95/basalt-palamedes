-- This module is the root of the `Palamedes` library: importing it brings the full public API
-- into scope — the `generator_search` tactic (via `Synthesizer`) and the runnable sampler
-- (`Sample`). The example corpus and the extraction audit live in the `PalamedesTest` library.
import Palamedes.Synthesizer
import Palamedes.Sample
import Palamedes.Stats
import Palamedes.Derive
