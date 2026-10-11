import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv308_c0 : below iv308.lo (caseIbQ (lookDT treeK) strsAll iv308.hi (iv308.p.getD 0 dPrm) (iv308.d.getD 0 [])) = true := by
  decide +kernel

theorem iv308_c1 : below iv308.lo (caseIIQ (lookDT treeK) admPre strsAll iv308.hi (iv308.p.getD 1 dPrm) (iv308.d.getD 1 [])) = true := by
  decide +kernel

theorem iv308_c2 : below iv308.lo (caseIII1Q (lookDT treeK) admPre strsAll iv308.hi (iv308.p.getD 2 dPrm) (iv308.d.getD 2 [])) = true := by
  decide +kernel

theorem iv308_c3 : below iv308.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv308.hi (iv308.p.getD 3 dPrm) (iv308.d.getD 3 [])) = true := by
  decide +kernel

theorem iv308_c4 : below iv308.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv308.hi (iv308.p.getD 4 dPrm) (iv308.d.getD 4 []) (iv308.d.getD 5 [])) = true := by
  decide +kernel

theorem iv308_ok : checkIv2 (lookDT treeK) admPre strsAll iv308 = true :=
  checkIv2_of_cases _ _ _ iv308 rfl rfl (by decide +kernel) iv308_c0 iv308_c1 iv308_c2 iv308_c3 iv308_c4

end ErdosComp
