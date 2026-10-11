import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv26_c0 : below iv26.lo (caseIbQ (lookDT treeK) strsAll iv26.hi (iv26.p.getD 0 dPrm) (iv26.d.getD 0 [])) = true := by
  decide +kernel

theorem iv26_c1 : below iv26.lo (caseIIQ (lookDT treeK) admPre strsAll iv26.hi (iv26.p.getD 1 dPrm) (iv26.d.getD 1 [])) = true := by
  decide +kernel

theorem iv26_c2 : below iv26.lo (caseIII1Q (lookDT treeK) admPre strsAll iv26.hi (iv26.p.getD 2 dPrm) (iv26.d.getD 2 [])) = true := by
  decide +kernel

theorem iv26_c3 : below iv26.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv26.hi (iv26.p.getD 3 dPrm) (iv26.d.getD 3 [])) = true := by
  decide +kernel

theorem iv26_c4 : below iv26.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv26.hi (iv26.p.getD 4 dPrm) (iv26.d.getD 4 []) (iv26.d.getD 5 [])) = true := by
  decide +kernel

theorem iv26_ok : checkIv2 (lookDT treeK) admPre strsAll iv26 = true :=
  checkIv2_of_cases _ _ _ iv26 rfl rfl (by decide +kernel) iv26_c0 iv26_c1 iv26_c2 iv26_c3 iv26_c4

end ErdosComp
