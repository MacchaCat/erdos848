import Erdos848.K2.J048
import Erdos848.K2.J049
import Erdos848.K2.J050
import Erdos848.K2.J051

namespace ErdosComp

theorem ivs12_ok : ivs12.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs12, List.all_cons, List.all_nil, iv48_ok, iv49_ok, iv50_ok, iv51_ok, Bool.and_true]

end ErdosComp
