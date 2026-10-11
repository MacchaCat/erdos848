import Erdos848.K2.J040
import Erdos848.K2.J041
import Erdos848.K2.J042
import Erdos848.K2.J043

namespace ErdosComp

theorem ivs10_ok : ivs10.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs10, List.all_cons, List.all_nil, iv40_ok, iv41_ok, iv42_ok, iv43_ok, Bool.and_true]

end ErdosComp
