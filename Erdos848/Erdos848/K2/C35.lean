import Erdos848.K2.J140
import Erdos848.K2.J141
import Erdos848.K2.J142
import Erdos848.K2.J143

namespace ErdosComp

theorem ivs35_ok : ivs35.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs35, List.all_cons, List.all_nil, iv140_ok, iv141_ok, iv142_ok, iv143_ok, Bool.and_true]

end ErdosComp
