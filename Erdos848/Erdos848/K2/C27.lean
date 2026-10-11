import Erdos848.K2.J108
import Erdos848.K2.J109
import Erdos848.K2.J110
import Erdos848.K2.J111

namespace ErdosComp

theorem ivs27_ok : ivs27.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs27, List.all_cons, List.all_nil, iv108_ok, iv109_ok, iv110_ok, iv111_ok, Bool.and_true]

end ErdosComp
