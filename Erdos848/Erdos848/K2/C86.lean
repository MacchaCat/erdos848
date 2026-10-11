import Erdos848.K2.J344
import Erdos848.K2.J345

namespace ErdosComp

theorem ivs86_ok : ivs86.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs86, List.all_cons, List.all_nil, iv344_ok, iv345_ok, Bool.and_true]

end ErdosComp
