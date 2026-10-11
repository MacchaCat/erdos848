import Erdos848.K2.J076
import Erdos848.K2.J077
import Erdos848.K2.J078
import Erdos848.K2.J079

namespace ErdosComp

theorem ivs19_ok : ivs19.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs19, List.all_cons, List.all_nil, iv76_ok, iv77_ok, iv78_ok, iv79_ok, Bool.and_true]

end ErdosComp
