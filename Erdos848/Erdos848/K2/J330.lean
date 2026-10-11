import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv330_c0 : below iv330.lo (caseIbQ (lookDT treeK) strsAll iv330.hi (iv330.p.getD 0 dPrm) (iv330.d.getD 0 [])) = true := by
  decide +kernel

theorem iv330_c1 : below iv330.lo (caseIIQ (lookDT treeK) admPre strsAll iv330.hi (iv330.p.getD 1 dPrm) (iv330.d.getD 1 [])) = true := by
  decide +kernel

theorem iv330_c2 : below iv330.lo (caseIII1Q (lookDT treeK) admPre strsAll iv330.hi (iv330.p.getD 2 dPrm) (iv330.d.getD 2 [])) = true := by
  decide +kernel

theorem iv330_c3 : below iv330.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv330.hi (iv330.p.getD 3 dPrm) (iv330.d.getD 3 [])) = true := by
  decide +kernel

theorem iv330_c4 : below iv330.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv330.hi (iv330.p.getD 4 dPrm) (iv330.d.getD 4 []) (iv330.d.getD 5 [])) = true := by
  decide +kernel

theorem iv330_ok : checkIv2 (lookDT treeK) admPre strsAll iv330 = true :=
  checkIv2_of_cases _ _ _ iv330 rfl rfl (by decide +kernel) iv330_c0 iv330_c1 iv330_c2 iv330_c3 iv330_c4

end ErdosComp
