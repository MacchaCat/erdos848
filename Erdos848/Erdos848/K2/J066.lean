import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv66_c0 : below iv66.lo (caseIbQ (lookDT treeK) strsAll iv66.hi (iv66.p.getD 0 dPrm) (iv66.d.getD 0 [])) = true := by
  decide +kernel

theorem iv66_c1 : below iv66.lo (caseIIQ (lookDT treeK) admPre strsAll iv66.hi (iv66.p.getD 1 dPrm) (iv66.d.getD 1 [])) = true := by
  decide +kernel

theorem iv66_c2 : below iv66.lo (caseIII1Q (lookDT treeK) admPre strsAll iv66.hi (iv66.p.getD 2 dPrm) (iv66.d.getD 2 [])) = true := by
  decide +kernel

theorem iv66_c3 : below iv66.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv66.hi (iv66.p.getD 3 dPrm) (iv66.d.getD 3 [])) = true := by
  decide +kernel

theorem iv66_c4 : below iv66.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv66.hi (iv66.p.getD 4 dPrm) (iv66.d.getD 4 []) (iv66.d.getD 5 [])) = true := by
  decide +kernel

theorem iv66_ok : checkIv2 (lookDT treeK) admPre strsAll iv66 = true :=
  checkIv2_of_cases _ _ _ iv66 rfl rfl (by decide +kernel) iv66_c0 iv66_c1 iv66_c2 iv66_c3 iv66_c4

end ErdosComp
