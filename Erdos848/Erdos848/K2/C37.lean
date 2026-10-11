import Erdos848.K2.J148
import Erdos848.K2.J149
import Erdos848.K2.J150
import Erdos848.K2.J151

namespace ErdosComp

theorem ivs37_ok : ivs37.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs37, List.all_cons, List.all_nil, iv148_ok, iv149_ok, iv150_ok, iv151_ok, Bool.and_true]

end ErdosComp
