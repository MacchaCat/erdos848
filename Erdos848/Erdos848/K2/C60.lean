import Erdos848.K2.J240
import Erdos848.K2.J241
import Erdos848.K2.J242
import Erdos848.K2.J243

namespace ErdosComp

theorem ivs60_ok : ivs60.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs60, List.all_cons, List.all_nil, iv240_ok, iv241_ok, iv242_ok, iv243_ok, Bool.and_true]

end ErdosComp
