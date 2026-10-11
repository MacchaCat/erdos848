import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv124_c0 : below iv124.lo (caseIbQ (lookDT treeK) strsAll iv124.hi (iv124.p.getD 0 dPrm) (iv124.d.getD 0 [])) = true := by
  decide +kernel

theorem iv124_c1 : below iv124.lo (caseIIQ (lookDT treeK) admPre strsAll iv124.hi (iv124.p.getD 1 dPrm) (iv124.d.getD 1 [])) = true := by
  decide +kernel

theorem iv124_c2 : below iv124.lo (caseIII1Q (lookDT treeK) admPre strsAll iv124.hi (iv124.p.getD 2 dPrm) (iv124.d.getD 2 [])) = true := by
  decide +kernel

theorem iv124_c3 : below iv124.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv124.hi (iv124.p.getD 3 dPrm) (iv124.d.getD 3 [])) = true := by
  decide +kernel

theorem iv124_c4 : below iv124.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv124.hi (iv124.p.getD 4 dPrm) (iv124.d.getD 4 []) (iv124.d.getD 5 [])) = true := by
  decide +kernel

theorem iv124_ok : checkIv2 (lookDT treeK) admPre strsAll iv124 = true :=
  checkIv2_of_cases _ _ _ iv124 rfl rfl (by decide +kernel) iv124_c0 iv124_c1 iv124_c2 iv124_c3 iv124_c4

end ErdosComp
