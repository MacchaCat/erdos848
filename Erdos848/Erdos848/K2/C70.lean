import Erdos848.K2.J280
import Erdos848.K2.J281
import Erdos848.K2.J282
import Erdos848.K2.J283

namespace ErdosComp

theorem ivs70_ok : ivs70.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs70, List.all_cons, List.all_nil, iv280_ok, iv281_ok, iv282_ok, iv283_ok, Bool.and_true]

end ErdosComp
