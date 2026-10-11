import Erdos848.K2.J248
import Erdos848.K2.J249
import Erdos848.K2.J250
import Erdos848.K2.J251

namespace ErdosComp

theorem ivs62_ok : ivs62.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs62, List.all_cons, List.all_nil, iv248_ok, iv249_ok, iv250_ok, iv251_ok, Bool.and_true]

end ErdosComp
