import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv36_c0 : below iv36.lo (caseIbQ (lookDT treeK) strsAll iv36.hi (iv36.p.getD 0 dPrm) (iv36.d.getD 0 [])) = true := by
  decide +kernel

theorem iv36_c1 : below iv36.lo (caseIIQ (lookDT treeK) admPre strsAll iv36.hi (iv36.p.getD 1 dPrm) (iv36.d.getD 1 [])) = true := by
  decide +kernel

theorem iv36_c2 : below iv36.lo (caseIII1Q (lookDT treeK) admPre strsAll iv36.hi (iv36.p.getD 2 dPrm) (iv36.d.getD 2 [])) = true := by
  decide +kernel

theorem iv36_c3 : below iv36.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv36.hi (iv36.p.getD 3 dPrm) (iv36.d.getD 3 [])) = true := by
  decide +kernel

theorem iv36_c4 : below iv36.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv36.hi (iv36.p.getD 4 dPrm) (iv36.d.getD 4 []) (iv36.d.getD 5 [])) = true := by
  decide +kernel

theorem iv36_ok : checkIv2 (lookDT treeK) admPre strsAll iv36 = true :=
  checkIv2_of_cases _ _ _ iv36 rfl rfl (by decide +kernel) iv36_c0 iv36_c1 iv36_c2 iv36_c3 iv36_c4

end ErdosComp
