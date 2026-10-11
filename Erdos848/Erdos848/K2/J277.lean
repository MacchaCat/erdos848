import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv277_c0 : below iv277.lo (caseIbQ (lookDT treeK) strsAll iv277.hi (iv277.p.getD 0 dPrm) (iv277.d.getD 0 [])) = true := by
  decide +kernel

theorem iv277_c1 : below iv277.lo (caseIIQ (lookDT treeK) admPre strsAll iv277.hi (iv277.p.getD 1 dPrm) (iv277.d.getD 1 [])) = true := by
  decide +kernel

theorem iv277_c2 : below iv277.lo (caseIII1Q (lookDT treeK) admPre strsAll iv277.hi (iv277.p.getD 2 dPrm) (iv277.d.getD 2 [])) = true := by
  decide +kernel

theorem iv277_c3 : below iv277.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv277.hi (iv277.p.getD 3 dPrm) (iv277.d.getD 3 [])) = true := by
  decide +kernel

theorem iv277_c4 : below iv277.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv277.hi (iv277.p.getD 4 dPrm) (iv277.d.getD 4 []) (iv277.d.getD 5 [])) = true := by
  decide +kernel

theorem iv277_ok : checkIv2 (lookDT treeK) admPre strsAll iv277 = true :=
  checkIv2_of_cases _ _ _ iv277 rfl rfl (by decide +kernel) iv277_c0 iv277_c1 iv277_c2 iv277_c3 iv277_c4

end ErdosComp
