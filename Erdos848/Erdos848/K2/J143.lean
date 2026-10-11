import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv143_c0 : below iv143.lo (caseIbQ (lookDT treeK) strsAll iv143.hi (iv143.p.getD 0 dPrm) (iv143.d.getD 0 [])) = true := by
  decide +kernel

theorem iv143_c1 : below iv143.lo (caseIIQ (lookDT treeK) admPre strsAll iv143.hi (iv143.p.getD 1 dPrm) (iv143.d.getD 1 [])) = true := by
  decide +kernel

theorem iv143_c2 : below iv143.lo (caseIII1Q (lookDT treeK) admPre strsAll iv143.hi (iv143.p.getD 2 dPrm) (iv143.d.getD 2 [])) = true := by
  decide +kernel

theorem iv143_c3 : below iv143.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv143.hi (iv143.p.getD 3 dPrm) (iv143.d.getD 3 [])) = true := by
  decide +kernel

theorem iv143_c4 : below iv143.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv143.hi (iv143.p.getD 4 dPrm) (iv143.d.getD 4 []) (iv143.d.getD 5 [])) = true := by
  decide +kernel

theorem iv143_ok : checkIv2 (lookDT treeK) admPre strsAll iv143 = true :=
  checkIv2_of_cases _ _ _ iv143 rfl rfl (by decide +kernel) iv143_c0 iv143_c1 iv143_c2 iv143_c3 iv143_c4

end ErdosComp
