import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv95_c0 : below iv95.lo (caseIbQ (lookDT treeK) strsAll iv95.hi (iv95.p.getD 0 dPrm) (iv95.d.getD 0 [])) = true := by
  decide +kernel

theorem iv95_c1 : below iv95.lo (caseIIQ (lookDT treeK) admPre strsAll iv95.hi (iv95.p.getD 1 dPrm) (iv95.d.getD 1 [])) = true := by
  decide +kernel

theorem iv95_c2 : below iv95.lo (caseIII1Q (lookDT treeK) admPre strsAll iv95.hi (iv95.p.getD 2 dPrm) (iv95.d.getD 2 [])) = true := by
  decide +kernel

theorem iv95_c3 : below iv95.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv95.hi (iv95.p.getD 3 dPrm) (iv95.d.getD 3 [])) = true := by
  decide +kernel

theorem iv95_c4 : below iv95.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv95.hi (iv95.p.getD 4 dPrm) (iv95.d.getD 4 []) (iv95.d.getD 5 [])) = true := by
  decide +kernel

theorem iv95_ok : checkIv2 (lookDT treeK) admPre strsAll iv95 = true :=
  checkIv2_of_cases _ _ _ iv95 rfl rfl (by decide +kernel) iv95_c0 iv95_c1 iv95_c2 iv95_c3 iv95_c4

end ErdosComp
