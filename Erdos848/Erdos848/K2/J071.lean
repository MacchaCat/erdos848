import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv71_c0 : below iv71.lo (caseIbQ (lookDT treeK) strsAll iv71.hi (iv71.p.getD 0 dPrm) (iv71.d.getD 0 [])) = true := by
  decide +kernel

theorem iv71_c1 : below iv71.lo (caseIIQ (lookDT treeK) admPre strsAll iv71.hi (iv71.p.getD 1 dPrm) (iv71.d.getD 1 [])) = true := by
  decide +kernel

theorem iv71_c2 : below iv71.lo (caseIII1Q (lookDT treeK) admPre strsAll iv71.hi (iv71.p.getD 2 dPrm) (iv71.d.getD 2 [])) = true := by
  decide +kernel

theorem iv71_c3 : below iv71.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv71.hi (iv71.p.getD 3 dPrm) (iv71.d.getD 3 [])) = true := by
  decide +kernel

theorem iv71_c4 : below iv71.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv71.hi (iv71.p.getD 4 dPrm) (iv71.d.getD 4 []) (iv71.d.getD 5 [])) = true := by
  decide +kernel

theorem iv71_ok : checkIv2 (lookDT treeK) admPre strsAll iv71 = true :=
  checkIv2_of_cases _ _ _ iv71 rfl rfl (by decide +kernel) iv71_c0 iv71_c1 iv71_c2 iv71_c3 iv71_c4

end ErdosComp
