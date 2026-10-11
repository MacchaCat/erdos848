import Erdos848.K2.J272
import Erdos848.K2.J273
import Erdos848.K2.J274
import Erdos848.K2.J275

namespace ErdosComp

theorem ivs68_ok : ivs68.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs68, List.all_cons, List.all_nil, iv272_ok, iv273_ok, iv274_ok, iv275_ok, Bool.and_true]

end ErdosComp
