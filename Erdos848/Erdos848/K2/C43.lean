import Erdos848.K2.J172
import Erdos848.K2.J173
import Erdos848.K2.J174
import Erdos848.K2.J175

namespace ErdosComp

theorem ivs43_ok : ivs43.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs43, List.all_cons, List.all_nil, iv172_ok, iv173_ok, iv174_ok, iv175_ok, Bool.and_true]

end ErdosComp
