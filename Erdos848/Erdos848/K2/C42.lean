import Erdos848.K2.J168
import Erdos848.K2.J169
import Erdos848.K2.J170
import Erdos848.K2.J171

namespace ErdosComp

theorem ivs42_ok : ivs42.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs42, List.all_cons, List.all_nil, iv168_ok, iv169_ok, iv170_ok, iv171_ok, Bool.and_true]

end ErdosComp
