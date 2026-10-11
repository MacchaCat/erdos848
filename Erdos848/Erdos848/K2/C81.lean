import Erdos848.K2.J324
import Erdos848.K2.J325
import Erdos848.K2.J326
import Erdos848.K2.J327

namespace ErdosComp

theorem ivs81_ok : ivs81.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs81, List.all_cons, List.all_nil, iv324_ok, iv325_ok, iv326_ok, iv327_ok, Bool.and_true]

end ErdosComp
