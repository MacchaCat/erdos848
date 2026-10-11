import Erdos848.K2.J072
import Erdos848.K2.J073
import Erdos848.K2.J074
import Erdos848.K2.J075

namespace ErdosComp

theorem ivs18_ok : ivs18.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs18, List.all_cons, List.all_nil, iv72_ok, iv73_ok, iv74_ok, iv75_ok, Bool.and_true]

end ErdosComp
