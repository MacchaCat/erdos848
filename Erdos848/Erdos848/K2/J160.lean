import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv160_c0 : below iv160.lo (caseIbQ (lookDT treeK) strsAll iv160.hi (iv160.p.getD 0 dPrm) (iv160.d.getD 0 [])) = true := by
  decide +kernel

theorem iv160_c1 : below iv160.lo (caseIIQ (lookDT treeK) admPre strsAll iv160.hi (iv160.p.getD 1 dPrm) (iv160.d.getD 1 [])) = true := by
  decide +kernel

theorem iv160_c2 : below iv160.lo (caseIII1Q (lookDT treeK) admPre strsAll iv160.hi (iv160.p.getD 2 dPrm) (iv160.d.getD 2 [])) = true := by
  decide +kernel

theorem iv160_c3 : below iv160.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv160.hi (iv160.p.getD 3 dPrm) (iv160.d.getD 3 [])) = true := by
  decide +kernel

theorem iv160_c4 : below iv160.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv160.hi (iv160.p.getD 4 dPrm) (iv160.d.getD 4 []) (iv160.d.getD 5 [])) = true := by
  decide +kernel

theorem iv160_ok : checkIv2 (lookDT treeK) admPre strsAll iv160 = true :=
  checkIv2_of_cases _ _ _ iv160 rfl rfl (by decide +kernel) iv160_c0 iv160_c1 iv160_c2 iv160_c3 iv160_c4

end ErdosComp
