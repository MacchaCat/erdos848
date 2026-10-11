import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv266_c0 : below iv266.lo (caseIbQ (lookDT treeK) strsAll iv266.hi (iv266.p.getD 0 dPrm) (iv266.d.getD 0 [])) = true := by
  decide +kernel

theorem iv266_c1 : below iv266.lo (caseIIQ (lookDT treeK) admPre strsAll iv266.hi (iv266.p.getD 1 dPrm) (iv266.d.getD 1 [])) = true := by
  decide +kernel

theorem iv266_c2 : below iv266.lo (caseIII1Q (lookDT treeK) admPre strsAll iv266.hi (iv266.p.getD 2 dPrm) (iv266.d.getD 2 [])) = true := by
  decide +kernel

theorem iv266_c3 : below iv266.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv266.hi (iv266.p.getD 3 dPrm) (iv266.d.getD 3 [])) = true := by
  decide +kernel

theorem iv266_c4 : below iv266.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv266.hi (iv266.p.getD 4 dPrm) (iv266.d.getD 4 []) (iv266.d.getD 5 [])) = true := by
  decide +kernel

theorem iv266_ok : checkIv2 (lookDT treeK) admPre strsAll iv266 = true :=
  checkIv2_of_cases _ _ _ iv266 rfl rfl (by decide +kernel) iv266_c0 iv266_c1 iv266_c2 iv266_c3 iv266_c4

end ErdosComp
