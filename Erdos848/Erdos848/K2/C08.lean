import Erdos848.K2.J032
import Erdos848.K2.J033
import Erdos848.K2.J034
import Erdos848.K2.J035

namespace ErdosComp

theorem ivs8_ok : ivs8.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs8, List.all_cons, List.all_nil, iv32_ok, iv33_ok, iv34_ok, iv35_ok, Bool.and_true]

end ErdosComp
