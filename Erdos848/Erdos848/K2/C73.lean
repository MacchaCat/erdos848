import Erdos848.K2.J292
import Erdos848.K2.J293
import Erdos848.K2.J294
import Erdos848.K2.J295

namespace ErdosComp

theorem ivs73_ok : ivs73.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs73, List.all_cons, List.all_nil, iv292_ok, iv293_ok, iv294_ok, iv295_ok, Bool.and_true]

end ErdosComp
