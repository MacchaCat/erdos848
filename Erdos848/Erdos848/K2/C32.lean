import Erdos848.K2.J128
import Erdos848.K2.J129
import Erdos848.K2.J130
import Erdos848.K2.J131

namespace ErdosComp

theorem ivs32_ok : ivs32.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs32, List.all_cons, List.all_nil, iv128_ok, iv129_ok, iv130_ok, iv131_ok, Bool.and_true]

end ErdosComp
