import Erdos848.K2.J008
import Erdos848.K2.J009
import Erdos848.K2.J010
import Erdos848.K2.J011

namespace ErdosComp

theorem ivs2_ok : ivs2.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs2, List.all_cons, List.all_nil, iv8_ok, iv9_ok, iv10_ok, iv11_ok, Bool.and_true]

end ErdosComp
