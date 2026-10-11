import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv149_c0 : below iv149.lo (caseIbQ (lookDT treeK) strsAll iv149.hi (iv149.p.getD 0 dPrm) (iv149.d.getD 0 [])) = true := by
  decide +kernel

theorem iv149_c1 : below iv149.lo (caseIIQ (lookDT treeK) admPre strsAll iv149.hi (iv149.p.getD 1 dPrm) (iv149.d.getD 1 [])) = true := by
  decide +kernel

theorem iv149_c2 : below iv149.lo (caseIII1Q (lookDT treeK) admPre strsAll iv149.hi (iv149.p.getD 2 dPrm) (iv149.d.getD 2 [])) = true := by
  decide +kernel

theorem iv149_c3 : below iv149.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv149.hi (iv149.p.getD 3 dPrm) (iv149.d.getD 3 [])) = true := by
  decide +kernel

theorem iv149_c4 : below iv149.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv149.hi (iv149.p.getD 4 dPrm) (iv149.d.getD 4 []) (iv149.d.getD 5 [])) = true := by
  decide +kernel

theorem iv149_ok : checkIv2 (lookDT treeK) admPre strsAll iv149 = true :=
  checkIv2_of_cases _ _ _ iv149 rfl rfl (by decide +kernel) iv149_c0 iv149_c1 iv149_c2 iv149_c3 iv149_c4

end ErdosComp
