import Erdos848.K2.J096
import Erdos848.K2.J097
import Erdos848.K2.J098
import Erdos848.K2.J099

namespace ErdosComp

theorem ivs24_ok : ivs24.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs24, List.all_cons, List.all_nil, iv96_ok, iv97_ok, iv98_ok, iv99_ok, Bool.and_true]

end ErdosComp
