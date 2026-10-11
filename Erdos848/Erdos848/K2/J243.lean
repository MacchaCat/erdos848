import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv243_c0 : below iv243.lo (caseIbQ (lookDT treeK) strsAll iv243.hi (iv243.p.getD 0 dPrm) (iv243.d.getD 0 [])) = true := by
  decide +kernel

theorem iv243_c1 : below iv243.lo (caseIIQ (lookDT treeK) admPre strsAll iv243.hi (iv243.p.getD 1 dPrm) (iv243.d.getD 1 [])) = true := by
  decide +kernel

theorem iv243_c2 : below iv243.lo (caseIII1Q (lookDT treeK) admPre strsAll iv243.hi (iv243.p.getD 2 dPrm) (iv243.d.getD 2 [])) = true := by
  decide +kernel

theorem iv243_c3 : below iv243.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv243.hi (iv243.p.getD 3 dPrm) (iv243.d.getD 3 [])) = true := by
  decide +kernel

theorem iv243_c4 : below iv243.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv243.hi (iv243.p.getD 4 dPrm) (iv243.d.getD 4 []) (iv243.d.getD 5 [])) = true := by
  decide +kernel

theorem iv243_ok : checkIv2 (lookDT treeK) admPre strsAll iv243 = true :=
  checkIv2_of_cases _ _ _ iv243 rfl rfl (by decide +kernel) iv243_c0 iv243_c1 iv243_c2 iv243_c3 iv243_c4

end ErdosComp
