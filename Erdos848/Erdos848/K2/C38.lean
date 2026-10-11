import Erdos848.K2.J152
import Erdos848.K2.J153
import Erdos848.K2.J154
import Erdos848.K2.J155

namespace ErdosComp

theorem ivs38_ok : ivs38.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs38, List.all_cons, List.all_nil, iv152_ok, iv153_ok, iv154_ok, iv155_ok, Bool.and_true]

end ErdosComp
