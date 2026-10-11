import Erdos848.K2.J064
import Erdos848.K2.J065
import Erdos848.K2.J066
import Erdos848.K2.J067

namespace ErdosComp

theorem ivs16_ok : ivs16.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs16, List.all_cons, List.all_nil, iv64_ok, iv65_ok, iv66_ok, iv67_ok, Bool.and_true]

end ErdosComp
