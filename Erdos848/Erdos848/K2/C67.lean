import Erdos848.K2.J268
import Erdos848.K2.J269
import Erdos848.K2.J270
import Erdos848.K2.J271

namespace ErdosComp

theorem ivs67_ok : ivs67.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs67, List.all_cons, List.all_nil, iv268_ok, iv269_ok, iv270_ok, iv271_ok, Bool.and_true]

end ErdosComp
