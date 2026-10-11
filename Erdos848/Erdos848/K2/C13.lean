import Erdos848.K2.J052
import Erdos848.K2.J053
import Erdos848.K2.J054
import Erdos848.K2.J055

namespace ErdosComp

theorem ivs13_ok : ivs13.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs13, List.all_cons, List.all_nil, iv52_ok, iv53_ok, iv54_ok, iv55_ok, Bool.and_true]

end ErdosComp
