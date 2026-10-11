import Erdos848.K2.J264
import Erdos848.K2.J265
import Erdos848.K2.J266
import Erdos848.K2.J267

namespace ErdosComp

theorem ivs66_ok : ivs66.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs66, List.all_cons, List.all_nil, iv264_ok, iv265_ok, iv266_ok, iv267_ok, Bool.and_true]

end ErdosComp
