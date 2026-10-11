import Erdos848.K2.J196
import Erdos848.K2.J197
import Erdos848.K2.J198
import Erdos848.K2.J199

namespace ErdosComp

theorem ivs49_ok : ivs49.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs49, List.all_cons, List.all_nil, iv196_ok, iv197_ok, iv198_ok, iv199_ok, Bool.and_true]

end ErdosComp
