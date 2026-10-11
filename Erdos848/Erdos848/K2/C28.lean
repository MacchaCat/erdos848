import Erdos848.K2.J112
import Erdos848.K2.J113
import Erdos848.K2.J114
import Erdos848.K2.J115

namespace ErdosComp

theorem ivs28_ok : ivs28.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs28, List.all_cons, List.all_nil, iv112_ok, iv113_ok, iv114_ok, iv115_ok, Bool.and_true]

end ErdosComp
