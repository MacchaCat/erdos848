import Erdos848.K2.J092
import Erdos848.K2.J093
import Erdos848.K2.J094
import Erdos848.K2.J095

namespace ErdosComp

theorem ivs23_ok : ivs23.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs23, List.all_cons, List.all_nil, iv92_ok, iv93_ok, iv94_ok, iv95_ok, Bool.and_true]

end ErdosComp
