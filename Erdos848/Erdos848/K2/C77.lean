import Erdos848.K2.J308
import Erdos848.K2.J309
import Erdos848.K2.J310
import Erdos848.K2.J311

namespace ErdosComp

theorem ivs77_ok : ivs77.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs77, List.all_cons, List.all_nil, iv308_ok, iv309_ok, iv310_ok, iv311_ok, Bool.and_true]

end ErdosComp
