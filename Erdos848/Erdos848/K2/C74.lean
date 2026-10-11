import Erdos848.K2.J296
import Erdos848.K2.J297
import Erdos848.K2.J298
import Erdos848.K2.J299

namespace ErdosComp

theorem ivs74_ok : ivs74.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs74, List.all_cons, List.all_nil, iv296_ok, iv297_ok, iv298_ok, iv299_ok, Bool.and_true]

end ErdosComp
