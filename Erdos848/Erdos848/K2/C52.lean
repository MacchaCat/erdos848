import Erdos848.K2.J208
import Erdos848.K2.J209
import Erdos848.K2.J210
import Erdos848.K2.J211

namespace ErdosComp

theorem ivs52_ok : ivs52.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs52, List.all_cons, List.all_nil, iv208_ok, iv209_ok, iv210_ok, iv211_ok, Bool.and_true]

end ErdosComp
