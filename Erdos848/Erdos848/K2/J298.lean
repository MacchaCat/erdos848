import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv298_c0 : below iv298.lo (caseIbQ (lookDT treeK) strsAll iv298.hi (iv298.p.getD 0 dPrm) (iv298.d.getD 0 [])) = true := by
  decide +kernel

theorem iv298_c1 : below iv298.lo (caseIIQ (lookDT treeK) admPre strsAll iv298.hi (iv298.p.getD 1 dPrm) (iv298.d.getD 1 [])) = true := by
  decide +kernel

theorem iv298_c2 : below iv298.lo (caseIII1Q (lookDT treeK) admPre strsAll iv298.hi (iv298.p.getD 2 dPrm) (iv298.d.getD 2 [])) = true := by
  decide +kernel

theorem iv298_c3 : below iv298.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv298.hi (iv298.p.getD 3 dPrm) (iv298.d.getD 3 [])) = true := by
  decide +kernel

theorem iv298_c4 : below iv298.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv298.hi (iv298.p.getD 4 dPrm) (iv298.d.getD 4 []) (iv298.d.getD 5 [])) = true := by
  decide +kernel

theorem iv298_ok : checkIv2 (lookDT treeK) admPre strsAll iv298 = true :=
  checkIv2_of_cases _ _ _ iv298 rfl rfl (by decide +kernel) iv298_c0 iv298_c1 iv298_c2 iv298_c3 iv298_c4

end ErdosComp
