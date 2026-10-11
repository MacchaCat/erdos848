import Erdos848.K2.J084
import Erdos848.K2.J085
import Erdos848.K2.J086
import Erdos848.K2.J087

namespace ErdosComp

theorem ivs21_ok : ivs21.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs21, List.all_cons, List.all_nil, iv84_ok, iv85_ok, iv86_ok, iv87_ok, Bool.and_true]

end ErdosComp
