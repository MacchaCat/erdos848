import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv291_c0 : below iv291.lo (caseIbQ (lookDT treeK) strsAll iv291.hi (iv291.p.getD 0 dPrm) (iv291.d.getD 0 [])) = true := by
  decide +kernel

theorem iv291_c1 : below iv291.lo (caseIIQ (lookDT treeK) admPre strsAll iv291.hi (iv291.p.getD 1 dPrm) (iv291.d.getD 1 [])) = true := by
  decide +kernel

theorem iv291_c2 : below iv291.lo (caseIII1Q (lookDT treeK) admPre strsAll iv291.hi (iv291.p.getD 2 dPrm) (iv291.d.getD 2 [])) = true := by
  decide +kernel

theorem iv291_c3 : below iv291.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv291.hi (iv291.p.getD 3 dPrm) (iv291.d.getD 3 [])) = true := by
  decide +kernel

theorem iv291_c4 : below iv291.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv291.hi (iv291.p.getD 4 dPrm) (iv291.d.getD 4 []) (iv291.d.getD 5 [])) = true := by
  decide +kernel

theorem iv291_ok : checkIv2 (lookDT treeK) admPre strsAll iv291 = true :=
  checkIv2_of_cases _ _ _ iv291 rfl rfl (by decide +kernel) iv291_c0 iv291_c1 iv291_c2 iv291_c3 iv291_c4

end ErdosComp
