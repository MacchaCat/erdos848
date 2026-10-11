import Erdos848.K2.J164
import Erdos848.K2.J165
import Erdos848.K2.J166
import Erdos848.K2.J167

namespace ErdosComp

theorem ivs41_ok : ivs41.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs41, List.all_cons, List.all_nil, iv164_ok, iv165_ok, iv166_ok, iv167_ok, Bool.and_true]

end ErdosComp
