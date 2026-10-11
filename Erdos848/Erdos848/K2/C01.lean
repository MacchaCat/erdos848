import Erdos848.K2.J004
import Erdos848.K2.J005
import Erdos848.K2.J006
import Erdos848.K2.J007

namespace ErdosComp

theorem ivs1_ok : ivs1.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs1, List.all_cons, List.all_nil, iv4_ok, iv5_ok, iv6_ok, iv7_ok, Bool.and_true]

end ErdosComp
