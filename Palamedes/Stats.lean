import Palamedes.Gen

/-!
# Statistics for Palamedes generators

Basalt's `#genstats` command draws from a generator many times and summarizes the distribution it
produces (see `Basalt.GenStats`). Its interpretation monad, `GenStats.StatGen`, is an instance of
Basalt's `Gen` typeclass; all a Palamedes generator additionally needs is a `Fail` instance, which
this file provides.

```
#genstats (genBST 0 10).run
#genstats (draws := 10000) (genRBT 4 0 10).run
```
-/

namespace Palamedes

/-- Computable failure for the statistics interpretation: a terminating failed draw, counted
    separately from fuel exhaustion. -/
instance : Fail GenStats.StatGen := ⟨throw (.failure "Gen.empty")⟩

/-- Interpret `g` at the statistics monad, for use with `#genstats`. -/
def toStatGen (g : Gen α) : GenStats.StatGen α := g.run

end Palamedes
