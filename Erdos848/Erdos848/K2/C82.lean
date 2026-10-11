import Erdos848.K2.J328
import Erdos848.K2.J329
import Erdos848.K2.J330
import Erdos848.K2.J331

namespace ErdosComp

theorem ivs82_ok : ivs82.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs82, List.all_cons, List.all_nil, iv328_ok, iv329_ok, iv330_ok, iv331_ok, Bool.and_true]

end ErdosComp
