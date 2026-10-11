import Erdos848.K2.J088
import Erdos848.K2.J089
import Erdos848.K2.J090
import Erdos848.K2.J091

namespace ErdosComp

theorem ivs22_ok : ivs22.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs22, List.all_cons, List.all_nil, iv88_ok, iv89_ok, iv90_ok, iv91_ok, Bool.and_true]

end ErdosComp
