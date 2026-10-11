import Erdos848.K2.J332
import Erdos848.K2.J333
import Erdos848.K2.J334
import Erdos848.K2.J335

namespace ErdosComp

theorem ivs83_ok : ivs83.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs83, List.all_cons, List.all_nil, iv332_ok, iv333_ok, iv334_ok, iv335_ok, Bool.and_true]

end ErdosComp
