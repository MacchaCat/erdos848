import Erdos848.K2.J060
import Erdos848.K2.J061
import Erdos848.K2.J062
import Erdos848.K2.J063

namespace ErdosComp

theorem ivs15_ok : ivs15.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs15, List.all_cons, List.all_nil, iv60_ok, iv61_ok, iv62_ok, iv63_ok, Bool.and_true]

end ErdosComp
