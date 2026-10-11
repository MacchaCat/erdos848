import Erdos848.K2.J020
import Erdos848.K2.J021
import Erdos848.K2.J022
import Erdos848.K2.J023

namespace ErdosComp

theorem ivs5_ok : ivs5.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs5, List.all_cons, List.all_nil, iv20_ok, iv21_ok, iv22_ok, iv23_ok, Bool.and_true]

end ErdosComp
