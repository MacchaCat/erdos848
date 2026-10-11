import Erdos848.K2.J176
import Erdos848.K2.J177
import Erdos848.K2.J178
import Erdos848.K2.J179

namespace ErdosComp

theorem ivs44_ok : ivs44.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs44, List.all_cons, List.all_nil, iv176_ok, iv177_ok, iv178_ok, iv179_ok, Bool.and_true]

end ErdosComp
