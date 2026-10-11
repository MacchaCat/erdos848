import Erdos848.K2.J024
import Erdos848.K2.J025
import Erdos848.K2.J026
import Erdos848.K2.J027

namespace ErdosComp

theorem ivs6_ok : ivs6.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs6, List.all_cons, List.all_nil, iv24_ok, iv25_ok, iv26_ok, iv27_ok, Bool.and_true]

end ErdosComp
