import Erdos848.K2.J080
import Erdos848.K2.J081
import Erdos848.K2.J082
import Erdos848.K2.J083

namespace ErdosComp

theorem ivs20_ok : ivs20.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs20, List.all_cons, List.all_nil, iv80_ok, iv81_ok, iv82_ok, iv83_ok, Bool.and_true]

end ErdosComp
