import Erdos848.K2.J124
import Erdos848.K2.J125
import Erdos848.K2.J126
import Erdos848.K2.J127

namespace ErdosComp

theorem ivs31_ok : ivs31.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs31, List.all_cons, List.all_nil, iv124_ok, iv125_ok, iv126_ok, iv127_ok, Bool.and_true]

end ErdosComp
