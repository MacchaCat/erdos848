import Erdos848.K2.J104
import Erdos848.K2.J105
import Erdos848.K2.J106
import Erdos848.K2.J107

namespace ErdosComp

theorem ivs26_ok : ivs26.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs26, List.all_cons, List.all_nil, iv104_ok, iv105_ok, iv106_ok, iv107_ok, Bool.and_true]

end ErdosComp
