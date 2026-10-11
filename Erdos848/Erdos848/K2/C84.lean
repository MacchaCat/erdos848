import Erdos848.K2.J336
import Erdos848.K2.J337
import Erdos848.K2.J338
import Erdos848.K2.J339

namespace ErdosComp

theorem ivs84_ok : ivs84.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs84, List.all_cons, List.all_nil, iv336_ok, iv337_ok, iv338_ok, iv339_ok, Bool.and_true]

end ErdosComp
