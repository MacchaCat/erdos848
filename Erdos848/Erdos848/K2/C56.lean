import Erdos848.K2.J224
import Erdos848.K2.J225
import Erdos848.K2.J226
import Erdos848.K2.J227

namespace ErdosComp

theorem ivs56_ok : ivs56.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs56, List.all_cons, List.all_nil, iv224_ok, iv225_ok, iv226_ok, iv227_ok, Bool.and_true]

end ErdosComp
