import Erdos848.K2.J188
import Erdos848.K2.J189
import Erdos848.K2.J190
import Erdos848.K2.J191

namespace ErdosComp

theorem ivs47_ok : ivs47.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs47, List.all_cons, List.all_nil, iv188_ok, iv189_ok, iv190_ok, iv191_ok, Bool.and_true]

end ErdosComp
