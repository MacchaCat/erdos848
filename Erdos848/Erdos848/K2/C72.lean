import Erdos848.K2.J288
import Erdos848.K2.J289
import Erdos848.K2.J290
import Erdos848.K2.J291

namespace ErdosComp

theorem ivs72_ok : ivs72.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs72, List.all_cons, List.all_nil, iv288_ok, iv289_ok, iv290_ok, iv291_ok, Bool.and_true]

end ErdosComp
