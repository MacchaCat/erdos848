import Erdos848.K2.J068
import Erdos848.K2.J069
import Erdos848.K2.J070
import Erdos848.K2.J071

namespace ErdosComp

theorem ivs17_ok : ivs17.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs17, List.all_cons, List.all_nil, iv68_ok, iv69_ok, iv70_ok, iv71_ok, Bool.and_true]

end ErdosComp
