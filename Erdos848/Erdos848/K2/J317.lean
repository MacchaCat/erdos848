import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv317_c0 : below iv317.lo (caseIbQ (lookDT treeK) strsAll iv317.hi (iv317.p.getD 0 dPrm) (iv317.d.getD 0 [])) = true := by
  decide +kernel

theorem iv317_c1 : below iv317.lo (caseIIQ (lookDT treeK) admPre strsAll iv317.hi (iv317.p.getD 1 dPrm) (iv317.d.getD 1 [])) = true := by
  decide +kernel

theorem iv317_c2 : below iv317.lo (caseIII1Q (lookDT treeK) admPre strsAll iv317.hi (iv317.p.getD 2 dPrm) (iv317.d.getD 2 [])) = true := by
  decide +kernel

theorem iv317_c3 : below iv317.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv317.hi (iv317.p.getD 3 dPrm) (iv317.d.getD 3 [])) = true := by
  decide +kernel

theorem iv317_c4 : below iv317.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv317.hi (iv317.p.getD 4 dPrm) (iv317.d.getD 4 []) (iv317.d.getD 5 [])) = true := by
  decide +kernel

theorem iv317_ok : checkIv2 (lookDT treeK) admPre strsAll iv317 = true :=
  checkIv2_of_cases _ _ _ iv317 rfl rfl (by decide +kernel) iv317_c0 iv317_c1 iv317_c2 iv317_c3 iv317_c4

end ErdosComp
