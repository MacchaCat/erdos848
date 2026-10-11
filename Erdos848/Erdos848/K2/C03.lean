import Erdos848.K2.J012
import Erdos848.K2.J013
import Erdos848.K2.J014
import Erdos848.K2.J015

namespace ErdosComp

theorem ivs3_ok : ivs3.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs3, List.all_cons, List.all_nil, iv12_ok, iv13_ok, iv14_ok, iv15_ok, Bool.and_true]

end ErdosComp
