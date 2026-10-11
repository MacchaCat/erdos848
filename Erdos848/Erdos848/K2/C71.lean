import Erdos848.K2.J284
import Erdos848.K2.J285
import Erdos848.K2.J286
import Erdos848.K2.J287

namespace ErdosComp

theorem ivs71_ok : ivs71.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs71, List.all_cons, List.all_nil, iv284_ok, iv285_ok, iv286_ok, iv287_ok, Bool.and_true]

end ErdosComp
