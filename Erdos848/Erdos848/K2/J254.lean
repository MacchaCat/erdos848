import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv254_c0 : below iv254.lo (caseIbQ (lookDT treeK) strsAll iv254.hi (iv254.p.getD 0 dPrm) (iv254.d.getD 0 [])) = true := by
  decide +kernel

theorem iv254_c1 : below iv254.lo (caseIIQ (lookDT treeK) admPre strsAll iv254.hi (iv254.p.getD 1 dPrm) (iv254.d.getD 1 [])) = true := by
  decide +kernel

theorem iv254_c2 : below iv254.lo (caseIII1Q (lookDT treeK) admPre strsAll iv254.hi (iv254.p.getD 2 dPrm) (iv254.d.getD 2 [])) = true := by
  decide +kernel

theorem iv254_c3 : below iv254.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv254.hi (iv254.p.getD 3 dPrm) (iv254.d.getD 3 [])) = true := by
  decide +kernel

theorem iv254_c4 : below iv254.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv254.hi (iv254.p.getD 4 dPrm) (iv254.d.getD 4 []) (iv254.d.getD 5 [])) = true := by
  decide +kernel

theorem iv254_ok : checkIv2 (lookDT treeK) admPre strsAll iv254 = true :=
  checkIv2_of_cases _ _ _ iv254 rfl rfl (by decide +kernel) iv254_c0 iv254_c1 iv254_c2 iv254_c3 iv254_c4

end ErdosComp
