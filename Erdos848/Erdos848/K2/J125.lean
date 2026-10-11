import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv125_c0 : below iv125.lo (caseIbQ (lookDT treeK) strsAll iv125.hi (iv125.p.getD 0 dPrm) (iv125.d.getD 0 [])) = true := by
  decide +kernel

theorem iv125_c1 : below iv125.lo (caseIIQ (lookDT treeK) admPre strsAll iv125.hi (iv125.p.getD 1 dPrm) (iv125.d.getD 1 [])) = true := by
  decide +kernel

theorem iv125_c2 : below iv125.lo (caseIII1Q (lookDT treeK) admPre strsAll iv125.hi (iv125.p.getD 2 dPrm) (iv125.d.getD 2 [])) = true := by
  decide +kernel

theorem iv125_c3 : below iv125.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv125.hi (iv125.p.getD 3 dPrm) (iv125.d.getD 3 [])) = true := by
  decide +kernel

theorem iv125_c4 : below iv125.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv125.hi (iv125.p.getD 4 dPrm) (iv125.d.getD 4 []) (iv125.d.getD 5 [])) = true := by
  decide +kernel

theorem iv125_ok : checkIv2 (lookDT treeK) admPre strsAll iv125 = true :=
  checkIv2_of_cases _ _ _ iv125 rfl rfl (by decide +kernel) iv125_c0 iv125_c1 iv125_c2 iv125_c3 iv125_c4

end ErdosComp
