import Erdos848.K2.J260
import Erdos848.K2.J261
import Erdos848.K2.J262
import Erdos848.K2.J263

namespace ErdosComp

theorem ivs65_ok : ivs65.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs65, List.all_cons, List.all_nil, iv260_ok, iv261_ok, iv262_ok, iv263_ok, Bool.and_true]

end ErdosComp
