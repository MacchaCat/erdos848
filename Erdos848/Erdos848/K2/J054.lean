import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv54_c0 : below iv54.lo (caseIbQ (lookDT treeK) strsAll iv54.hi (iv54.p.getD 0 dPrm) (iv54.d.getD 0 [])) = true := by
  decide +kernel

theorem iv54_c1 : below iv54.lo (caseIIQ (lookDT treeK) admPre strsAll iv54.hi (iv54.p.getD 1 dPrm) (iv54.d.getD 1 [])) = true := by
  decide +kernel

theorem iv54_c2 : below iv54.lo (caseIII1Q (lookDT treeK) admPre strsAll iv54.hi (iv54.p.getD 2 dPrm) (iv54.d.getD 2 [])) = true := by
  decide +kernel

theorem iv54_c3 : below iv54.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv54.hi (iv54.p.getD 3 dPrm) (iv54.d.getD 3 [])) = true := by
  decide +kernel

theorem iv54_c4 : below iv54.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv54.hi (iv54.p.getD 4 dPrm) (iv54.d.getD 4 []) (iv54.d.getD 5 [])) = true := by
  decide +kernel

theorem iv54_ok : checkIv2 (lookDT treeK) admPre strsAll iv54 = true :=
  checkIv2_of_cases _ _ _ iv54 rfl rfl (by decide +kernel) iv54_c0 iv54_c1 iv54_c2 iv54_c3 iv54_c4

end ErdosComp
