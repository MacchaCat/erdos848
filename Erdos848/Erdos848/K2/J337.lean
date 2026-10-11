import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv337_c0 : below iv337.lo (caseIbQ (lookDT treeK) strsAll iv337.hi (iv337.p.getD 0 dPrm) (iv337.d.getD 0 [])) = true := by
  decide +kernel

theorem iv337_c1 : below iv337.lo (caseIIQ (lookDT treeK) admPre strsAll iv337.hi (iv337.p.getD 1 dPrm) (iv337.d.getD 1 [])) = true := by
  decide +kernel

theorem iv337_c2 : below iv337.lo (caseIII1Q (lookDT treeK) admPre strsAll iv337.hi (iv337.p.getD 2 dPrm) (iv337.d.getD 2 [])) = true := by
  decide +kernel

theorem iv337_c3 : below iv337.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv337.hi (iv337.p.getD 3 dPrm) (iv337.d.getD 3 [])) = true := by
  decide +kernel

theorem iv337_c4 : below iv337.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv337.hi (iv337.p.getD 4 dPrm) (iv337.d.getD 4 []) (iv337.d.getD 5 [])) = true := by
  decide +kernel

theorem iv337_ok : checkIv2 (lookDT treeK) admPre strsAll iv337 = true :=
  checkIv2_of_cases _ _ _ iv337 rfl rfl (by decide +kernel) iv337_c0 iv337_c1 iv337_c2 iv337_c3 iv337_c4

end ErdosComp
