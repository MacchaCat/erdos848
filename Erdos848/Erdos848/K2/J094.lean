import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv94_c0 : below iv94.lo (caseIbQ (lookDT treeK) strsAll iv94.hi (iv94.p.getD 0 dPrm) (iv94.d.getD 0 [])) = true := by
  decide +kernel

theorem iv94_c1 : below iv94.lo (caseIIQ (lookDT treeK) admPre strsAll iv94.hi (iv94.p.getD 1 dPrm) (iv94.d.getD 1 [])) = true := by
  decide +kernel

theorem iv94_c2 : below iv94.lo (caseIII1Q (lookDT treeK) admPre strsAll iv94.hi (iv94.p.getD 2 dPrm) (iv94.d.getD 2 [])) = true := by
  decide +kernel

theorem iv94_c3 : below iv94.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv94.hi (iv94.p.getD 3 dPrm) (iv94.d.getD 3 [])) = true := by
  decide +kernel

theorem iv94_c4 : below iv94.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv94.hi (iv94.p.getD 4 dPrm) (iv94.d.getD 4 []) (iv94.d.getD 5 [])) = true := by
  decide +kernel

theorem iv94_ok : checkIv2 (lookDT treeK) admPre strsAll iv94 = true :=
  checkIv2_of_cases _ _ _ iv94 rfl rfl (by decide +kernel) iv94_c0 iv94_c1 iv94_c2 iv94_c3 iv94_c4

end ErdosComp
