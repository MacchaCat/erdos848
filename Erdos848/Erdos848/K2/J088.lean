import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv88_c0 : below iv88.lo (caseIbQ (lookDT treeK) strsAll iv88.hi (iv88.p.getD 0 dPrm) (iv88.d.getD 0 [])) = true := by
  decide +kernel

theorem iv88_c1 : below iv88.lo (caseIIQ (lookDT treeK) admPre strsAll iv88.hi (iv88.p.getD 1 dPrm) (iv88.d.getD 1 [])) = true := by
  decide +kernel

theorem iv88_c2 : below iv88.lo (caseIII1Q (lookDT treeK) admPre strsAll iv88.hi (iv88.p.getD 2 dPrm) (iv88.d.getD 2 [])) = true := by
  decide +kernel

theorem iv88_c3 : below iv88.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv88.hi (iv88.p.getD 3 dPrm) (iv88.d.getD 3 [])) = true := by
  decide +kernel

theorem iv88_c4 : below iv88.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv88.hi (iv88.p.getD 4 dPrm) (iv88.d.getD 4 []) (iv88.d.getD 5 [])) = true := by
  decide +kernel

theorem iv88_ok : checkIv2 (lookDT treeK) admPre strsAll iv88 = true :=
  checkIv2_of_cases _ _ _ iv88 rfl rfl (by decide +kernel) iv88_c0 iv88_c1 iv88_c2 iv88_c3 iv88_c4

end ErdosComp
