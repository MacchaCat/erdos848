import Erdos848.K2.J232
import Erdos848.K2.J233
import Erdos848.K2.J234
import Erdos848.K2.J235

namespace ErdosComp

theorem ivs58_ok : ivs58.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs58, List.all_cons, List.all_nil, iv232_ok, iv233_ok, iv234_ok, iv235_ok, Bool.and_true]

end ErdosComp
