import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv29_c0 : below iv29.lo (caseIbQ (lookDT treeK) strsAll iv29.hi (iv29.p.getD 0 dPrm) (iv29.d.getD 0 [])) = true := by
  decide +kernel

theorem iv29_c1 : below iv29.lo (caseIIQ (lookDT treeK) admPre strsAll iv29.hi (iv29.p.getD 1 dPrm) (iv29.d.getD 1 [])) = true := by
  decide +kernel

theorem iv29_c2 : below iv29.lo (caseIII1Q (lookDT treeK) admPre strsAll iv29.hi (iv29.p.getD 2 dPrm) (iv29.d.getD 2 [])) = true := by
  decide +kernel

theorem iv29_c3 : below iv29.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv29.hi (iv29.p.getD 3 dPrm) (iv29.d.getD 3 [])) = true := by
  decide +kernel

theorem iv29_c4 : below iv29.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv29.hi (iv29.p.getD 4 dPrm) (iv29.d.getD 4 []) (iv29.d.getD 5 [])) = true := by
  decide +kernel

theorem iv29_ok : checkIv2 (lookDT treeK) admPre strsAll iv29 = true :=
  checkIv2_of_cases _ _ _ iv29 rfl rfl (by decide +kernel) iv29_c0 iv29_c1 iv29_c2 iv29_c3 iv29_c4

end ErdosComp
