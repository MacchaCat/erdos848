import Erdos848.K2.J216
import Erdos848.K2.J217
import Erdos848.K2.J218
import Erdos848.K2.J219

namespace ErdosComp

theorem ivs54_ok : ivs54.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs54, List.all_cons, List.all_nil, iv216_ok, iv217_ok, iv218_ok, iv219_ok, Bool.and_true]

end ErdosComp
