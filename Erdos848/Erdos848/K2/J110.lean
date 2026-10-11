import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv110_c0 : below iv110.lo (caseIbQ (lookDT treeK) strsAll iv110.hi (iv110.p.getD 0 dPrm) (iv110.d.getD 0 [])) = true := by
  decide +kernel

theorem iv110_c1 : below iv110.lo (caseIIQ (lookDT treeK) admPre strsAll iv110.hi (iv110.p.getD 1 dPrm) (iv110.d.getD 1 [])) = true := by
  decide +kernel

theorem iv110_c2 : below iv110.lo (caseIII1Q (lookDT treeK) admPre strsAll iv110.hi (iv110.p.getD 2 dPrm) (iv110.d.getD 2 [])) = true := by
  decide +kernel

theorem iv110_c3 : below iv110.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv110.hi (iv110.p.getD 3 dPrm) (iv110.d.getD 3 [])) = true := by
  decide +kernel

theorem iv110_c4 : below iv110.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv110.hi (iv110.p.getD 4 dPrm) (iv110.d.getD 4 []) (iv110.d.getD 5 [])) = true := by
  decide +kernel

theorem iv110_ok : checkIv2 (lookDT treeK) admPre strsAll iv110 = true :=
  checkIv2_of_cases _ _ _ iv110 rfl rfl (by decide +kernel) iv110_c0 iv110_c1 iv110_c2 iv110_c3 iv110_c4

end ErdosComp
