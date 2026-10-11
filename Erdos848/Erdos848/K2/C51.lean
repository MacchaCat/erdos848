import Erdos848.K2.J204
import Erdos848.K2.J205
import Erdos848.K2.J206
import Erdos848.K2.J207

namespace ErdosComp

theorem ivs51_ok : ivs51.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs51, List.all_cons, List.all_nil, iv204_ok, iv205_ok, iv206_ok, iv207_ok, Bool.and_true]

end ErdosComp
