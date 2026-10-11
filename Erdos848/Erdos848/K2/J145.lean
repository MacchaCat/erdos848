import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv145_c0 : below iv145.lo (caseIbQ (lookDT treeK) strsAll iv145.hi (iv145.p.getD 0 dPrm) (iv145.d.getD 0 [])) = true := by
  decide +kernel

theorem iv145_c1 : below iv145.lo (caseIIQ (lookDT treeK) admPre strsAll iv145.hi (iv145.p.getD 1 dPrm) (iv145.d.getD 1 [])) = true := by
  decide +kernel

theorem iv145_c2 : below iv145.lo (caseIII1Q (lookDT treeK) admPre strsAll iv145.hi (iv145.p.getD 2 dPrm) (iv145.d.getD 2 [])) = true := by
  decide +kernel

theorem iv145_c3 : below iv145.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv145.hi (iv145.p.getD 3 dPrm) (iv145.d.getD 3 [])) = true := by
  decide +kernel

theorem iv145_c4 : below iv145.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv145.hi (iv145.p.getD 4 dPrm) (iv145.d.getD 4 []) (iv145.d.getD 5 [])) = true := by
  decide +kernel

theorem iv145_ok : checkIv2 (lookDT treeK) admPre strsAll iv145 = true :=
  checkIv2_of_cases _ _ _ iv145 rfl rfl (by decide +kernel) iv145_c0 iv145_c1 iv145_c2 iv145_c3 iv145_c4

end ErdosComp
