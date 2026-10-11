import Erdos848.K2.J304
import Erdos848.K2.J305
import Erdos848.K2.J306
import Erdos848.K2.J307

namespace ErdosComp

theorem ivs76_ok : ivs76.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs76, List.all_cons, List.all_nil, iv304_ok, iv305_ok, iv306_ok, iv307_ok, Bool.and_true]

end ErdosComp
