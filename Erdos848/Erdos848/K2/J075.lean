import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv75_c0 : below iv75.lo (caseIbQ (lookDT treeK) strsAll iv75.hi (iv75.p.getD 0 dPrm) (iv75.d.getD 0 [])) = true := by
  decide +kernel

theorem iv75_c1 : below iv75.lo (caseIIQ (lookDT treeK) admPre strsAll iv75.hi (iv75.p.getD 1 dPrm) (iv75.d.getD 1 [])) = true := by
  decide +kernel

theorem iv75_c2 : below iv75.lo (caseIII1Q (lookDT treeK) admPre strsAll iv75.hi (iv75.p.getD 2 dPrm) (iv75.d.getD 2 [])) = true := by
  decide +kernel

theorem iv75_c3 : below iv75.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv75.hi (iv75.p.getD 3 dPrm) (iv75.d.getD 3 [])) = true := by
  decide +kernel

theorem iv75_c4 : below iv75.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv75.hi (iv75.p.getD 4 dPrm) (iv75.d.getD 4 []) (iv75.d.getD 5 [])) = true := by
  decide +kernel

theorem iv75_ok : checkIv2 (lookDT treeK) admPre strsAll iv75 = true :=
  checkIv2_of_cases _ _ _ iv75 rfl rfl (by decide +kernel) iv75_c0 iv75_c1 iv75_c2 iv75_c3 iv75_c4

end ErdosComp
