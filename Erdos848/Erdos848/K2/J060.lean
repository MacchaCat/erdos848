import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv60_c0 : below iv60.lo (caseIbQ (lookDT treeK) strsAll iv60.hi (iv60.p.getD 0 dPrm) (iv60.d.getD 0 [])) = true := by
  decide +kernel

theorem iv60_c1 : below iv60.lo (caseIIQ (lookDT treeK) admPre strsAll iv60.hi (iv60.p.getD 1 dPrm) (iv60.d.getD 1 [])) = true := by
  decide +kernel

theorem iv60_c2 : below iv60.lo (caseIII1Q (lookDT treeK) admPre strsAll iv60.hi (iv60.p.getD 2 dPrm) (iv60.d.getD 2 [])) = true := by
  decide +kernel

theorem iv60_c3 : below iv60.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv60.hi (iv60.p.getD 3 dPrm) (iv60.d.getD 3 [])) = true := by
  decide +kernel

theorem iv60_c4 : below iv60.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv60.hi (iv60.p.getD 4 dPrm) (iv60.d.getD 4 []) (iv60.d.getD 5 [])) = true := by
  decide +kernel

theorem iv60_ok : checkIv2 (lookDT treeK) admPre strsAll iv60 = true :=
  checkIv2_of_cases _ _ _ iv60 rfl rfl (by decide +kernel) iv60_c0 iv60_c1 iv60_c2 iv60_c3 iv60_c4

end ErdosComp
