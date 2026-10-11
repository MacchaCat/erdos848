import Erdos848.K2.J256
import Erdos848.K2.J257
import Erdos848.K2.J258
import Erdos848.K2.J259

namespace ErdosComp

theorem ivs64_ok : ivs64.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs64, List.all_cons, List.all_nil, iv256_ok, iv257_ok, iv258_ok, iv259_ok, Bool.and_true]

end ErdosComp
