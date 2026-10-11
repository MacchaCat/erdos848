import Erdos848.K2.J316
import Erdos848.K2.J317
import Erdos848.K2.J318
import Erdos848.K2.J319

namespace ErdosComp

theorem ivs79_ok : ivs79.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs79, List.all_cons, List.all_nil, iv316_ok, iv317_ok, iv318_ok, iv319_ok, Bool.and_true]

end ErdosComp
