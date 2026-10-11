import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv301_c0 : below iv301.lo (caseIbQ (lookDT treeK) strsAll iv301.hi (iv301.p.getD 0 dPrm) (iv301.d.getD 0 [])) = true := by
  decide +kernel

theorem iv301_c1 : below iv301.lo (caseIIQ (lookDT treeK) admPre strsAll iv301.hi (iv301.p.getD 1 dPrm) (iv301.d.getD 1 [])) = true := by
  decide +kernel

theorem iv301_c2 : below iv301.lo (caseIII1Q (lookDT treeK) admPre strsAll iv301.hi (iv301.p.getD 2 dPrm) (iv301.d.getD 2 [])) = true := by
  decide +kernel

theorem iv301_c3 : below iv301.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv301.hi (iv301.p.getD 3 dPrm) (iv301.d.getD 3 [])) = true := by
  decide +kernel

theorem iv301_c4 : below iv301.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv301.hi (iv301.p.getD 4 dPrm) (iv301.d.getD 4 []) (iv301.d.getD 5 [])) = true := by
  decide +kernel

theorem iv301_ok : checkIv2 (lookDT treeK) admPre strsAll iv301 = true :=
  checkIv2_of_cases _ _ _ iv301 rfl rfl (by decide +kernel) iv301_c0 iv301_c1 iv301_c2 iv301_c3 iv301_c4

end ErdosComp
