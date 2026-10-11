import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv147_c0 : below iv147.lo (caseIbQ (lookDT treeK) strsAll iv147.hi (iv147.p.getD 0 dPrm) (iv147.d.getD 0 [])) = true := by
  decide +kernel

theorem iv147_c1 : below iv147.lo (caseIIQ (lookDT treeK) admPre strsAll iv147.hi (iv147.p.getD 1 dPrm) (iv147.d.getD 1 [])) = true := by
  decide +kernel

theorem iv147_c2 : below iv147.lo (caseIII1Q (lookDT treeK) admPre strsAll iv147.hi (iv147.p.getD 2 dPrm) (iv147.d.getD 2 [])) = true := by
  decide +kernel

theorem iv147_c3 : below iv147.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv147.hi (iv147.p.getD 3 dPrm) (iv147.d.getD 3 [])) = true := by
  decide +kernel

theorem iv147_c4 : below iv147.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv147.hi (iv147.p.getD 4 dPrm) (iv147.d.getD 4 []) (iv147.d.getD 5 [])) = true := by
  decide +kernel

theorem iv147_ok : checkIv2 (lookDT treeK) admPre strsAll iv147 = true :=
  checkIv2_of_cases _ _ _ iv147 rfl rfl (by decide +kernel) iv147_c0 iv147_c1 iv147_c2 iv147_c3 iv147_c4

end ErdosComp
