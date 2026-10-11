import Erdos848.K2.J200
import Erdos848.K2.J201
import Erdos848.K2.J202
import Erdos848.K2.J203

namespace ErdosComp

theorem ivs50_ok : ivs50.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs50, List.all_cons, List.all_nil, iv200_ok, iv201_ok, iv202_ok, iv203_ok, Bool.and_true]

end ErdosComp
