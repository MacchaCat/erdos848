import Erdos848.K2.J120
import Erdos848.K2.J121
import Erdos848.K2.J122
import Erdos848.K2.J123

namespace ErdosComp

theorem ivs30_ok : ivs30.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs30, List.all_cons, List.all_nil, iv120_ok, iv121_ok, iv122_ok, iv123_ok, Bool.and_true]

end ErdosComp
