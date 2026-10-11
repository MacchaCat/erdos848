import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv140_c0 : below iv140.lo (caseIbQ (lookDT treeK) strsAll iv140.hi (iv140.p.getD 0 dPrm) (iv140.d.getD 0 [])) = true := by
  decide +kernel

theorem iv140_c1 : below iv140.lo (caseIIQ (lookDT treeK) admPre strsAll iv140.hi (iv140.p.getD 1 dPrm) (iv140.d.getD 1 [])) = true := by
  decide +kernel

theorem iv140_c2 : below iv140.lo (caseIII1Q (lookDT treeK) admPre strsAll iv140.hi (iv140.p.getD 2 dPrm) (iv140.d.getD 2 [])) = true := by
  decide +kernel

theorem iv140_c3 : below iv140.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv140.hi (iv140.p.getD 3 dPrm) (iv140.d.getD 3 [])) = true := by
  decide +kernel

theorem iv140_c4 : below iv140.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv140.hi (iv140.p.getD 4 dPrm) (iv140.d.getD 4 []) (iv140.d.getD 5 [])) = true := by
  decide +kernel

theorem iv140_ok : checkIv2 (lookDT treeK) admPre strsAll iv140 = true :=
  checkIv2_of_cases _ _ _ iv140 rfl rfl (by decide +kernel) iv140_c0 iv140_c1 iv140_c2 iv140_c3 iv140_c4

end ErdosComp
