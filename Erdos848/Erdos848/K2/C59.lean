import Erdos848.K2.J236
import Erdos848.K2.J237
import Erdos848.K2.J238
import Erdos848.K2.J239

namespace ErdosComp

theorem ivs59_ok : ivs59.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs59, List.all_cons, List.all_nil, iv236_ok, iv237_ok, iv238_ok, iv239_ok, Bool.and_true]

end ErdosComp
