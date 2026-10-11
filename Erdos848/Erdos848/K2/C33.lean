import Erdos848.K2.J132
import Erdos848.K2.J133
import Erdos848.K2.J134
import Erdos848.K2.J135

namespace ErdosComp

theorem ivs33_ok : ivs33.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs33, List.all_cons, List.all_nil, iv132_ok, iv133_ok, iv134_ok, iv135_ok, Bool.and_true]

end ErdosComp
