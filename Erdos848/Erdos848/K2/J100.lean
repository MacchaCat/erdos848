import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv100_c0 : below iv100.lo (caseIbQ (lookDT treeK) strsAll iv100.hi (iv100.p.getD 0 dPrm) (iv100.d.getD 0 [])) = true := by
  decide +kernel

theorem iv100_c1 : below iv100.lo (caseIIQ (lookDT treeK) admPre strsAll iv100.hi (iv100.p.getD 1 dPrm) (iv100.d.getD 1 [])) = true := by
  decide +kernel

theorem iv100_c2 : below iv100.lo (caseIII1Q (lookDT treeK) admPre strsAll iv100.hi (iv100.p.getD 2 dPrm) (iv100.d.getD 2 [])) = true := by
  decide +kernel

theorem iv100_c3 : below iv100.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv100.hi (iv100.p.getD 3 dPrm) (iv100.d.getD 3 [])) = true := by
  decide +kernel

theorem iv100_c4 : below iv100.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv100.hi (iv100.p.getD 4 dPrm) (iv100.d.getD 4 []) (iv100.d.getD 5 [])) = true := by
  decide +kernel

theorem iv100_ok : checkIv2 (lookDT treeK) admPre strsAll iv100 = true :=
  checkIv2_of_cases _ _ _ iv100 rfl rfl (by decide +kernel) iv100_c0 iv100_c1 iv100_c2 iv100_c3 iv100_c4

end ErdosComp
