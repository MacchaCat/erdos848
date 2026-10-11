import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv231_c0 : below iv231.lo (caseIbQ (lookDT treeK) strsAll iv231.hi (iv231.p.getD 0 dPrm) (iv231.d.getD 0 [])) = true := by
  decide +kernel

theorem iv231_c1 : below iv231.lo (caseIIQ (lookDT treeK) admPre strsAll iv231.hi (iv231.p.getD 1 dPrm) (iv231.d.getD 1 [])) = true := by
  decide +kernel

theorem iv231_c2 : below iv231.lo (caseIII1Q (lookDT treeK) admPre strsAll iv231.hi (iv231.p.getD 2 dPrm) (iv231.d.getD 2 [])) = true := by
  decide +kernel

theorem iv231_c3 : below iv231.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv231.hi (iv231.p.getD 3 dPrm) (iv231.d.getD 3 [])) = true := by
  decide +kernel

theorem iv231_c4 : below iv231.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv231.hi (iv231.p.getD 4 dPrm) (iv231.d.getD 4 []) (iv231.d.getD 5 [])) = true := by
  decide +kernel

theorem iv231_ok : checkIv2 (lookDT treeK) admPre strsAll iv231 = true :=
  checkIv2_of_cases _ _ _ iv231 rfl rfl (by decide +kernel) iv231_c0 iv231_c1 iv231_c2 iv231_c3 iv231_c4

end ErdosComp
