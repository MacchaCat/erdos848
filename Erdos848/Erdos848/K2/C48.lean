import Erdos848.K2.J192
import Erdos848.K2.J193
import Erdos848.K2.J194
import Erdos848.K2.J195

namespace ErdosComp

theorem ivs48_ok : ivs48.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs48, List.all_cons, List.all_nil, iv192_ok, iv193_ok, iv194_ok, iv195_ok, Bool.and_true]

end ErdosComp
