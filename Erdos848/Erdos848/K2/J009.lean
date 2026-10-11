import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv9_c0 : below iv9.lo (caseIbQ (lookDT treeK) strsAll iv9.hi (iv9.p.getD 0 dPrm) (iv9.d.getD 0 [])) = true := by
  decide +kernel

theorem iv9_c1 : below iv9.lo (caseIIQ (lookDT treeK) admPre strsAll iv9.hi (iv9.p.getD 1 dPrm) (iv9.d.getD 1 [])) = true := by
  decide +kernel

theorem iv9_c2 : below iv9.lo (caseIII1Q (lookDT treeK) admPre strsAll iv9.hi (iv9.p.getD 2 dPrm) (iv9.d.getD 2 [])) = true := by
  decide +kernel

theorem iv9_c3 : below iv9.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv9.hi (iv9.p.getD 3 dPrm) (iv9.d.getD 3 [])) = true := by
  decide +kernel

theorem iv9_c4 : below iv9.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv9.hi (iv9.p.getD 4 dPrm) (iv9.d.getD 4 []) (iv9.d.getD 5 [])) = true := by
  decide +kernel

theorem iv9_ok : checkIv2 (lookDT treeK) admPre strsAll iv9 = true :=
  checkIv2_of_cases _ _ _ iv9 rfl rfl (by decide +kernel) iv9_c0 iv9_c1 iv9_c2 iv9_c3 iv9_c4

end ErdosComp
