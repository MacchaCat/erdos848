import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv45_c0 : below iv45.lo (caseIbQ (lookDT treeK) strsAll iv45.hi (iv45.p.getD 0 dPrm) (iv45.d.getD 0 [])) = true := by
  decide +kernel

theorem iv45_c1 : below iv45.lo (caseIIQ (lookDT treeK) admPre strsAll iv45.hi (iv45.p.getD 1 dPrm) (iv45.d.getD 1 [])) = true := by
  decide +kernel

theorem iv45_c2 : below iv45.lo (caseIII1Q (lookDT treeK) admPre strsAll iv45.hi (iv45.p.getD 2 dPrm) (iv45.d.getD 2 [])) = true := by
  decide +kernel

theorem iv45_c3 : below iv45.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv45.hi (iv45.p.getD 3 dPrm) (iv45.d.getD 3 [])) = true := by
  decide +kernel

theorem iv45_c4 : below iv45.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv45.hi (iv45.p.getD 4 dPrm) (iv45.d.getD 4 []) (iv45.d.getD 5 [])) = true := by
  decide +kernel

theorem iv45_ok : checkIv2 (lookDT treeK) admPre strsAll iv45 = true :=
  checkIv2_of_cases _ _ _ iv45 rfl rfl (by decide +kernel) iv45_c0 iv45_c1 iv45_c2 iv45_c3 iv45_c4

end ErdosComp
