import Erdos848.K2.J100
import Erdos848.K2.J101
import Erdos848.K2.J102
import Erdos848.K2.J103

namespace ErdosComp

theorem ivs25_ok : ivs25.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs25, List.all_cons, List.all_nil, iv100_ok, iv101_ok, iv102_ok, iv103_ok, Bool.and_true]

end ErdosComp
