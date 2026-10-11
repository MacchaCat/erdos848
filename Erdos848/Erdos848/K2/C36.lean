import Erdos848.K2.J144
import Erdos848.K2.J145
import Erdos848.K2.J146
import Erdos848.K2.J147

namespace ErdosComp

theorem ivs36_ok : ivs36.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs36, List.all_cons, List.all_nil, iv144_ok, iv145_ok, iv146_ok, iv147_ok, Bool.and_true]

end ErdosComp
