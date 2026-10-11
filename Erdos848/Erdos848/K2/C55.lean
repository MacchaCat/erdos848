import Erdos848.K2.J220
import Erdos848.K2.J221
import Erdos848.K2.J222
import Erdos848.K2.J223

namespace ErdosComp

theorem ivs55_ok : ivs55.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs55, List.all_cons, List.all_nil, iv220_ok, iv221_ok, iv222_ok, iv223_ok, Bool.and_true]

end ErdosComp
