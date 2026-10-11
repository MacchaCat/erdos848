import Erdos848.K2.J244
import Erdos848.K2.J245
import Erdos848.K2.J246
import Erdos848.K2.J247

namespace ErdosComp

theorem ivs61_ok : ivs61.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs61, List.all_cons, List.all_nil, iv244_ok, iv245_ok, iv246_ok, iv247_ok, Bool.and_true]

end ErdosComp
