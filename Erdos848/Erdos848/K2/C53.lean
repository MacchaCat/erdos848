import Erdos848.K2.J212
import Erdos848.K2.J213
import Erdos848.K2.J214
import Erdos848.K2.J215

namespace ErdosComp

theorem ivs53_ok : ivs53.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs53, List.all_cons, List.all_nil, iv212_ok, iv213_ok, iv214_ok, iv215_ok, Bool.and_true]

end ErdosComp
