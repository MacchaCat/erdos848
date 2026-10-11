import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv34_c0 : below iv34.lo (caseIbQ (lookDT treeK) strsAll iv34.hi (iv34.p.getD 0 dPrm) (iv34.d.getD 0 [])) = true := by
  decide +kernel

theorem iv34_c1 : below iv34.lo (caseIIQ (lookDT treeK) admPre strsAll iv34.hi (iv34.p.getD 1 dPrm) (iv34.d.getD 1 [])) = true := by
  decide +kernel

theorem iv34_c2 : below iv34.lo (caseIII1Q (lookDT treeK) admPre strsAll iv34.hi (iv34.p.getD 2 dPrm) (iv34.d.getD 2 [])) = true := by
  decide +kernel

theorem iv34_c3 : below iv34.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv34.hi (iv34.p.getD 3 dPrm) (iv34.d.getD 3 [])) = true := by
  decide +kernel

theorem iv34_c4 : below iv34.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv34.hi (iv34.p.getD 4 dPrm) (iv34.d.getD 4 []) (iv34.d.getD 5 [])) = true := by
  decide +kernel

theorem iv34_ok : checkIv2 (lookDT treeK) admPre strsAll iv34 = true :=
  checkIv2_of_cases _ _ _ iv34 rfl rfl (by decide +kernel) iv34_c0 iv34_c1 iv34_c2 iv34_c3 iv34_c4

end ErdosComp
