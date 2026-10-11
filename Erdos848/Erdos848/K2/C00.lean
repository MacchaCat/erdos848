import Erdos848.K2.J000
import Erdos848.K2.J001
import Erdos848.K2.J002
import Erdos848.K2.J003

namespace ErdosComp

theorem ivs0_ok : ivs0.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs0, List.all_cons, List.all_nil, iv0_ok, iv1_ok, iv2_ok, iv3_ok, Bool.and_true]

end ErdosComp
