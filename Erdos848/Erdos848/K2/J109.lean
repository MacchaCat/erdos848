import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv109_c0 : below iv109.lo (caseIbQ (lookDT treeK) strsAll iv109.hi (iv109.p.getD 0 dPrm) (iv109.d.getD 0 [])) = true := by
  decide +kernel

theorem iv109_c1 : below iv109.lo (caseIIQ (lookDT treeK) admPre strsAll iv109.hi (iv109.p.getD 1 dPrm) (iv109.d.getD 1 [])) = true := by
  decide +kernel

theorem iv109_c2 : below iv109.lo (caseIII1Q (lookDT treeK) admPre strsAll iv109.hi (iv109.p.getD 2 dPrm) (iv109.d.getD 2 [])) = true := by
  decide +kernel

theorem iv109_c3 : below iv109.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv109.hi (iv109.p.getD 3 dPrm) (iv109.d.getD 3 [])) = true := by
  decide +kernel

theorem iv109_c4 : below iv109.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv109.hi (iv109.p.getD 4 dPrm) (iv109.d.getD 4 []) (iv109.d.getD 5 [])) = true := by
  decide +kernel

theorem iv109_ok : checkIv2 (lookDT treeK) admPre strsAll iv109 = true :=
  checkIv2_of_cases _ _ _ iv109 rfl rfl (by decide +kernel) iv109_c0 iv109_c1 iv109_c2 iv109_c3 iv109_c4

end ErdosComp
