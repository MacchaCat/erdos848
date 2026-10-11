import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv338_c0 : below iv338.lo (caseIbQ (lookDT treeK) strsAll iv338.hi (iv338.p.getD 0 dPrm) (iv338.d.getD 0 [])) = true := by
  decide +kernel

theorem iv338_c1 : below iv338.lo (caseIIQ (lookDT treeK) admPre strsAll iv338.hi (iv338.p.getD 1 dPrm) (iv338.d.getD 1 [])) = true := by
  decide +kernel

theorem iv338_c2 : below iv338.lo (caseIII1Q (lookDT treeK) admPre strsAll iv338.hi (iv338.p.getD 2 dPrm) (iv338.d.getD 2 [])) = true := by
  decide +kernel

theorem iv338_c3 : below iv338.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv338.hi (iv338.p.getD 3 dPrm) (iv338.d.getD 3 [])) = true := by
  decide +kernel

theorem iv338_c4 : below iv338.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv338.hi (iv338.p.getD 4 dPrm) (iv338.d.getD 4 []) (iv338.d.getD 5 [])) = true := by
  decide +kernel

theorem iv338_ok : checkIv2 (lookDT treeK) admPre strsAll iv338 = true :=
  checkIv2_of_cases _ _ _ iv338 rfl rfl (by decide +kernel) iv338_c0 iv338_c1 iv338_c2 iv338_c3 iv338_c4

end ErdosComp
