import Erdos848.K2.J160
import Erdos848.K2.J161
import Erdos848.K2.J162
import Erdos848.K2.J163

namespace ErdosComp

theorem ivs40_ok : ivs40.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs40, List.all_cons, List.all_nil, iv160_ok, iv161_ok, iv162_ok, iv163_ok, Bool.and_true]

end ErdosComp
