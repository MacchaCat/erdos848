import Erdos848.K2.J320
import Erdos848.K2.J321
import Erdos848.K2.J322
import Erdos848.K2.J323

namespace ErdosComp

theorem ivs80_ok : ivs80.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs80, List.all_cons, List.all_nil, iv320_ok, iv321_ok, iv322_ok, iv323_ok, Bool.and_true]

end ErdosComp
