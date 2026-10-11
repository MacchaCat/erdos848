import Erdos848.K2.J300
import Erdos848.K2.J301
import Erdos848.K2.J302
import Erdos848.K2.J303

namespace ErdosComp

theorem ivs75_ok : ivs75.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs75, List.all_cons, List.all_nil, iv300_ok, iv301_ok, iv302_ok, iv303_ok, Bool.and_true]

end ErdosComp
