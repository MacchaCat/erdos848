import Erdos848.K2.J156
import Erdos848.K2.J157
import Erdos848.K2.J158
import Erdos848.K2.J159

namespace ErdosComp

theorem ivs39_ok : ivs39.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs39, List.all_cons, List.all_nil, iv156_ok, iv157_ok, iv158_ok, iv159_ok, Bool.and_true]

end ErdosComp
