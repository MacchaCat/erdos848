import Erdos848.K2.J136
import Erdos848.K2.J137
import Erdos848.K2.J138
import Erdos848.K2.J139

namespace ErdosComp

theorem ivs34_ok : ivs34.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs34, List.all_cons, List.all_nil, iv136_ok, iv137_ok, iv138_ok, iv139_ok, Bool.and_true]

end ErdosComp
