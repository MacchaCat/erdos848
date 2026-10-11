import Erdos848.K2.J276
import Erdos848.K2.J277
import Erdos848.K2.J278
import Erdos848.K2.J279

namespace ErdosComp

theorem ivs69_ok : ivs69.all (checkIv2 (lookDT treeK) admPre strsAll) = true := by
  simp only [ivs69, List.all_cons, List.all_nil, iv276_ok, iv277_ok, iv278_ok, iv279_ok, Bool.and_true]

end ErdosComp
