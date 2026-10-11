import Erdos848.K2.J180
import Erdos848.K2.J181
import Erdos848.K2.J182
import Erdos848.K2.J183

namespace ErdosComp

theorem ivs45_ok : ivs45.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs45, List.all_cons, List.all_nil, iv180_ok, iv181_ok, iv182_ok, iv183_ok, Bool.and_true]

end ErdosComp
