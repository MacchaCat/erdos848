import Erdos848.K2.J228
import Erdos848.K2.J229
import Erdos848.K2.J230
import Erdos848.K2.J231

namespace ErdosComp

theorem ivs57_ok : ivs57.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs57, List.all_cons, List.all_nil, iv228_ok, iv229_ok, iv230_ok, iv231_ok, Bool.and_true]

end ErdosComp
