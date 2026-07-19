import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Total
import Palamedes.RuleSets

namespace Palamedes

open _root_.Palamedes.Gen

namespace Gen

@[reducible, extract]
def arbUnit : Gen Unit := pure ()

namespace CorrectGen

@[extract, aesop safe apply (rule_sets := [synthesis])]
def s_arbUnit : @CorrectGen Unit (fun _ => True) :=
  Subtype.mk arbUnit (by simp [arbUnit])

end CorrectGen

namespace Total

@[total]
def total_arbUnit : total arbUnit :=
  total_pure ()

end Total

end Gen

end Palamedes
