import Erdos848.K2.J184
import Erdos848.K2.J185
import Erdos848.K2.J186
import Erdos848.K2.J187

namespace ErdosComp

theorem ivs46_ok : ivs46.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs46, List.all_cons, List.all_nil, iv184_ok, iv185_ok, iv186_ok, iv187_ok, Bool.and_true]

end ErdosComp
