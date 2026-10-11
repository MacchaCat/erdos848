import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv35_c0 : below iv35.lo (caseIbQ (lookDT treeK) strsAll iv35.hi (iv35.p.getD 0 dPrm) (iv35.d.getD 0 [])) = true := by
  decide +kernel

theorem iv35_c1 : below iv35.lo (caseIIQ (lookDT treeK) admPre strsAll iv35.hi (iv35.p.getD 1 dPrm) (iv35.d.getD 1 [])) = true := by
  decide +kernel

theorem iv35_c2 : below iv35.lo (caseIII1Q (lookDT treeK) admPre strsAll iv35.hi (iv35.p.getD 2 dPrm) (iv35.d.getD 2 [])) = true := by
  decide +kernel

theorem iv35_c3 : below iv35.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv35.hi (iv35.p.getD 3 dPrm) (iv35.d.getD 3 [])) = true := by
  decide +kernel

theorem iv35_c4 : below iv35.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv35.hi (iv35.p.getD 4 dPrm) (iv35.d.getD 4 []) (iv35.d.getD 5 [])) = true := by
  decide +kernel

theorem iv35_ok : checkIv2 (lookDT treeK) admPre strsAll iv35 = true :=
  checkIv2_of_cases _ _ _ iv35 rfl rfl (by decide +kernel) iv35_c0 iv35_c1 iv35_c2 iv35_c3 iv35_c4

end ErdosComp
