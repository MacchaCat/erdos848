import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv344_c0 : below iv344.lo (caseIbQ (lookDT treeK) strsAll iv344.hi (iv344.p.getD 0 dPrm) (iv344.d.getD 0 [])) = true := by
  decide +kernel

theorem iv344_c1 : below iv344.lo (caseIIQ (lookDT treeK) admPre strsAll iv344.hi (iv344.p.getD 1 dPrm) (iv344.d.getD 1 [])) = true := by
  decide +kernel

theorem iv344_c2 : below iv344.lo (caseIII1Q (lookDT treeK) admPre strsAll iv344.hi (iv344.p.getD 2 dPrm) (iv344.d.getD 2 [])) = true := by
  decide +kernel

theorem iv344_c3 : below iv344.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv344.hi (iv344.p.getD 3 dPrm) (iv344.d.getD 3 [])) = true := by
  decide +kernel

theorem iv344_c4 : below iv344.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv344.hi (iv344.p.getD 4 dPrm) (iv344.d.getD 4 []) (iv344.d.getD 5 [])) = true := by
  decide +kernel

theorem iv344_ok : checkIv2 (lookDT treeK) admPre strsAll iv344 = true :=
  checkIv2_of_cases _ _ _ iv344 rfl rfl (by decide +kernel) iv344_c0 iv344_c1 iv344_c2 iv344_c3 iv344_c4

end ErdosComp
