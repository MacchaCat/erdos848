import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv130_c0 : below iv130.lo (caseIbQ (lookDT treeK) strsAll iv130.hi (iv130.p.getD 0 dPrm) (iv130.d.getD 0 [])) = true := by
  decide +kernel

theorem iv130_c1 : below iv130.lo (caseIIQ (lookDT treeK) admPre strsAll iv130.hi (iv130.p.getD 1 dPrm) (iv130.d.getD 1 [])) = true := by
  decide +kernel

theorem iv130_c2 : below iv130.lo (caseIII1Q (lookDT treeK) admPre strsAll iv130.hi (iv130.p.getD 2 dPrm) (iv130.d.getD 2 [])) = true := by
  decide +kernel

theorem iv130_c3 : below iv130.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv130.hi (iv130.p.getD 3 dPrm) (iv130.d.getD 3 [])) = true := by
  decide +kernel

theorem iv130_c4 : below iv130.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv130.hi (iv130.p.getD 4 dPrm) (iv130.d.getD 4 []) (iv130.d.getD 5 [])) = true := by
  decide +kernel

theorem iv130_ok : checkIv2 (lookDT treeK) admPre strsAll iv130 = true :=
  checkIv2_of_cases _ _ _ iv130 rfl rfl (by decide +kernel) iv130_c0 iv130_c1 iv130_c2 iv130_c3 iv130_c4

end ErdosComp
