import Erdos848.K2.J016
import Erdos848.K2.J017
import Erdos848.K2.J018
import Erdos848.K2.J019

namespace ErdosComp

theorem ivs4_ok : ivs4.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs4, List.all_cons, List.all_nil, iv16_ok, iv17_ok, iv18_ok, iv19_ok, Bool.and_true]

end ErdosComp
