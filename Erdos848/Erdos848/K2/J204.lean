import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv204_c0 : below iv204.lo (caseIbQ (lookDT treeK) strsAll iv204.hi (iv204.p.getD 0 dPrm) (iv204.d.getD 0 [])) = true := by
  decide +kernel

theorem iv204_c1 : below iv204.lo (caseIIQ (lookDT treeK) admPre strsAll iv204.hi (iv204.p.getD 1 dPrm) (iv204.d.getD 1 [])) = true := by
  decide +kernel

theorem iv204_c2 : below iv204.lo (caseIII1Q (lookDT treeK) admPre strsAll iv204.hi (iv204.p.getD 2 dPrm) (iv204.d.getD 2 [])) = true := by
  decide +kernel

theorem iv204_c3 : below iv204.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv204.hi (iv204.p.getD 3 dPrm) (iv204.d.getD 3 [])) = true := by
  decide +kernel

theorem iv204_c4 : below iv204.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv204.hi (iv204.p.getD 4 dPrm) (iv204.d.getD 4 []) (iv204.d.getD 5 [])) = true := by
  decide +kernel

theorem iv204_ok : checkIv2 (lookDT treeK) admPre strsAll iv204 = true :=
  checkIv2_of_cases _ _ _ iv204 rfl rfl (by decide +kernel) iv204_c0 iv204_c1 iv204_c2 iv204_c3 iv204_c4

end ErdosComp
