import Erdos848.K2.J116
import Erdos848.K2.J117
import Erdos848.K2.J118
import Erdos848.K2.J119

namespace ErdosComp

theorem ivs29_ok : ivs29.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs29, List.all_cons, List.all_nil, iv116_ok, iv117_ok, iv118_ok, iv119_ok, Bool.and_true]

end ErdosComp
