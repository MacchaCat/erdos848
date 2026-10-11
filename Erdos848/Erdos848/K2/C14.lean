import Erdos848.K2.J056
import Erdos848.K2.J057
import Erdos848.K2.J058
import Erdos848.K2.J059

namespace ErdosComp

theorem ivs14_ok : ivs14.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs14, List.all_cons, List.all_nil, iv56_ok, iv57_ok, iv58_ok, iv59_ok, Bool.and_true]

end ErdosComp
