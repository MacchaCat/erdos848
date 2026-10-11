import Erdos848.K2.J252
import Erdos848.K2.J253
import Erdos848.K2.J254
import Erdos848.K2.J255

namespace ErdosComp

theorem ivs63_ok : ivs63.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs63, List.all_cons, List.all_nil, iv252_ok, iv253_ok, iv254_ok, iv255_ok, Bool.and_true]

end ErdosComp
