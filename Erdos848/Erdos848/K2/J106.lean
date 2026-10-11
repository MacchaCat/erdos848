import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv106_c0 : below iv106.lo (caseIbQ (lookDT treeK) strsAll iv106.hi (iv106.p.getD 0 dPrm) (iv106.d.getD 0 [])) = true := by
  decide +kernel

theorem iv106_c1 : below iv106.lo (caseIIQ (lookDT treeK) admPre strsAll iv106.hi (iv106.p.getD 1 dPrm) (iv106.d.getD 1 [])) = true := by
  decide +kernel

theorem iv106_c2 : below iv106.lo (caseIII1Q (lookDT treeK) admPre strsAll iv106.hi (iv106.p.getD 2 dPrm) (iv106.d.getD 2 [])) = true := by
  decide +kernel

theorem iv106_c3 : below iv106.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv106.hi (iv106.p.getD 3 dPrm) (iv106.d.getD 3 [])) = true := by
  decide +kernel

theorem iv106_c4 : below iv106.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv106.hi (iv106.p.getD 4 dPrm) (iv106.d.getD 4 []) (iv106.d.getD 5 [])) = true := by
  decide +kernel

theorem iv106_ok : checkIv2 (lookDT treeK) admPre strsAll iv106 = true :=
  checkIv2_of_cases _ _ _ iv106 rfl rfl (by decide +kernel) iv106_c0 iv106_c1 iv106_c2 iv106_c3 iv106_c4

end ErdosComp
