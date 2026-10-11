import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv225_c0 : below iv225.lo (caseIbQ (lookDT treeK) strsAll iv225.hi (iv225.p.getD 0 dPrm) (iv225.d.getD 0 [])) = true := by
  decide +kernel

theorem iv225_c1 : below iv225.lo (caseIIQ (lookDT treeK) admPre strsAll iv225.hi (iv225.p.getD 1 dPrm) (iv225.d.getD 1 [])) = true := by
  decide +kernel

theorem iv225_c2 : below iv225.lo (caseIII1Q (lookDT treeK) admPre strsAll iv225.hi (iv225.p.getD 2 dPrm) (iv225.d.getD 2 [])) = true := by
  decide +kernel

theorem iv225_c3 : below iv225.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv225.hi (iv225.p.getD 3 dPrm) (iv225.d.getD 3 [])) = true := by
  decide +kernel

theorem iv225_c4 : below iv225.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv225.hi (iv225.p.getD 4 dPrm) (iv225.d.getD 4 []) (iv225.d.getD 5 [])) = true := by
  decide +kernel

theorem iv225_ok : checkIv2 (lookDT treeK) admPre strsAll iv225 = true :=
  checkIv2_of_cases _ _ _ iv225 rfl rfl (by decide +kernel) iv225_c0 iv225_c1 iv225_c2 iv225_c3 iv225_c4

end ErdosComp
