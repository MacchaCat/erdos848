import Erdos848.K2.J312
import Erdos848.K2.J313
import Erdos848.K2.J314
import Erdos848.K2.J315

namespace ErdosComp

theorem ivs78_ok : ivs78.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs78, List.all_cons, List.all_nil, iv312_ok, iv313_ok, iv314_ok, iv315_ok, Bool.and_true]

end ErdosComp
