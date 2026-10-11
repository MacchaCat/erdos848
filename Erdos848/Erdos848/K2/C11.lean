import Erdos848.K2.J044
import Erdos848.K2.J045
import Erdos848.K2.J046
import Erdos848.K2.J047

namespace ErdosComp

theorem ivs11_ok : ivs11.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs11, List.all_cons, List.all_nil, iv44_ok, iv45_ok, iv46_ok, iv47_ok, Bool.and_true]

end ErdosComp
