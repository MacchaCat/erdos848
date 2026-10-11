import Erdos848.K2.J340
import Erdos848.K2.J341
import Erdos848.K2.J342
import Erdos848.K2.J343

namespace ErdosComp

theorem ivs85_ok : ivs85.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs85, List.all_cons, List.all_nil, iv340_ok, iv341_ok, iv342_ok, iv343_ok, Bool.and_true]

end ErdosComp
