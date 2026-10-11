import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv285_c0 : below iv285.lo (caseIbQ (lookDT treeK) strsAll iv285.hi (iv285.p.getD 0 dPrm) (iv285.d.getD 0 [])) = true := by
  decide +kernel

theorem iv285_c1 : below iv285.lo (caseIIQ (lookDT treeK) admPre strsAll iv285.hi (iv285.p.getD 1 dPrm) (iv285.d.getD 1 [])) = true := by
  decide +kernel

theorem iv285_c2 : below iv285.lo (caseIII1Q (lookDT treeK) admPre strsAll iv285.hi (iv285.p.getD 2 dPrm) (iv285.d.getD 2 [])) = true := by
  decide +kernel

theorem iv285_c3 : below iv285.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv285.hi (iv285.p.getD 3 dPrm) (iv285.d.getD 3 [])) = true := by
  decide +kernel

theorem iv285_c4 : below iv285.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv285.hi (iv285.p.getD 4 dPrm) (iv285.d.getD 4 []) (iv285.d.getD 5 [])) = true := by
  decide +kernel

theorem iv285_ok : checkIv2 (lookDT treeK) admPre strsAll iv285 = true :=
  checkIv2_of_cases _ _ _ iv285 rfl rfl (by decide +kernel) iv285_c0 iv285_c1 iv285_c2 iv285_c3 iv285_c4

end ErdosComp
