import Palamedes.Gen
import Palamedes.CorrectGen
import Palamedes.Total

namespace Gen

@[reducible]
def arbUnit : Gen Unit := pure ()

namespace CorrectGen

def s_arbUnit : @CorrectGen Unit (fun _ => True) :=
  Subtype.mk arbUnit (by simp [arbUnit])

@[extract]
theorem s_arbUnit_val : s_arbUnit.val = pure () := rfl

end CorrectGen

end Gen
