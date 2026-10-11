import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv24_c0 : below iv24.lo (caseIbQ (lookDT treeK) strsAll iv24.hi (iv24.p.getD 0 dPrm) (iv24.d.getD 0 [])) = true := by
  decide +kernel

theorem iv24_c1 : below iv24.lo (caseIIQ (lookDT treeK) admPre strsAll iv24.hi (iv24.p.getD 1 dPrm) (iv24.d.getD 1 [])) = true := by
  decide +kernel

theorem iv24_c2 : below iv24.lo (caseIII1Q (lookDT treeK) admPre strsAll iv24.hi (iv24.p.getD 2 dPrm) (iv24.d.getD 2 [])) = true := by
  decide +kernel

theorem iv24_c3 : below iv24.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv24.hi (iv24.p.getD 3 dPrm) (iv24.d.getD 3 [])) = true := by
  decide +kernel

theorem iv24_c4 : below iv24.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv24.hi (iv24.p.getD 4 dPrm) (iv24.d.getD 4 []) (iv24.d.getD 5 [])) = true := by
  decide +kernel

theorem iv24_ok : checkIv2 (lookDT treeK) admPre strsAll iv24 = true :=
  checkIv2_of_cases _ _ _ iv24 rfl rfl (by decide +kernel) iv24_c0 iv24_c1 iv24_c2 iv24_c3 iv24_c4

end ErdosComp
