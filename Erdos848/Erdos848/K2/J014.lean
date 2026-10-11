import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv14_c0 : below iv14.lo (caseIbQ (lookDT treeK) strsAll iv14.hi (iv14.p.getD 0 dPrm) (iv14.d.getD 0 [])) = true := by
  decide +kernel

theorem iv14_c1 : below iv14.lo (caseIIQ (lookDT treeK) admPre strsAll iv14.hi (iv14.p.getD 1 dPrm) (iv14.d.getD 1 [])) = true := by
  decide +kernel

theorem iv14_c2 : below iv14.lo (caseIII1Q (lookDT treeK) admPre strsAll iv14.hi (iv14.p.getD 2 dPrm) (iv14.d.getD 2 [])) = true := by
  decide +kernel

theorem iv14_c3 : below iv14.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv14.hi (iv14.p.getD 3 dPrm) (iv14.d.getD 3 [])) = true := by
  decide +kernel

theorem iv14_c4 : below iv14.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv14.hi (iv14.p.getD 4 dPrm) (iv14.d.getD 4 []) (iv14.d.getD 5 [])) = true := by
  decide +kernel

theorem iv14_ok : checkIv2 (lookDT treeK) admPre strsAll iv14 = true :=
  checkIv2_of_cases _ _ _ iv14 rfl rfl (by decide +kernel) iv14_c0 iv14_c1 iv14_c2 iv14_c3 iv14_c4

end ErdosComp
