import Erdos848.K2.J028
import Erdos848.K2.J029
import Erdos848.K2.J030
import Erdos848.K2.J031

namespace ErdosComp

theorem ivs7_ok : ivs7.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs7, List.all_cons, List.all_nil, iv28_ok, iv29_ok, iv30_ok, iv31_ok, Bool.and_true]

end ErdosComp
