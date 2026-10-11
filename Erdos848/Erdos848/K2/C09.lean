import Erdos848.K2.J036
import Erdos848.K2.J037
import Erdos848.K2.J038
import Erdos848.K2.J039

namespace ErdosComp

theorem ivs9_ok : ivs9.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs9, List.all_cons, List.all_nil, iv36_ok, iv37_ok, iv38_ok, iv39_ok, Bool.and_true]

end ErdosComp
