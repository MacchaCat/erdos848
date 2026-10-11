import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv113_c0 : below iv113.lo (caseIbQ (lookDT treeK) strsAll iv113.hi (iv113.p.getD 0 dPrm) (iv113.d.getD 0 [])) = true := by
  decide +kernel

theorem iv113_c1 : below iv113.lo (caseIIQ (lookDT treeK) admPre strsAll iv113.hi (iv113.p.getD 1 dPrm) (iv113.d.getD 1 [])) = true := by
  decide +kernel

theorem iv113_c2 : below iv113.lo (caseIII1Q (lookDT treeK) admPre strsAll iv113.hi (iv113.p.getD 2 dPrm) (iv113.d.getD 2 [])) = true := by
  decide +kernel

theorem iv113_c3 : below iv113.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv113.hi (iv113.p.getD 3 dPrm) (iv113.d.getD 3 [])) = true := by
  decide +kernel

theorem iv113_c4 : below iv113.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv113.hi (iv113.p.getD 4 dPrm) (iv113.d.getD 4 []) (iv113.d.getD 5 [])) = true := by
  decide +kernel

theorem iv113_ok : checkIv2 (lookDT treeK) admPre strsAll iv113 = true :=
  checkIv2_of_cases _ _ _ iv113 rfl rfl (by decide +kernel) iv113_c0 iv113_c1 iv113_c2 iv113_c3 iv113_c4

end ErdosComp
