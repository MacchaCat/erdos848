import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv246_c0 : below iv246.lo (caseIbQ (lookDT treeK) strsAll iv246.hi (iv246.p.getD 0 dPrm) (iv246.d.getD 0 [])) = true := by
  decide +kernel

theorem iv246_c1 : below iv246.lo (caseIIQ (lookDT treeK) admPre strsAll iv246.hi (iv246.p.getD 1 dPrm) (iv246.d.getD 1 [])) = true := by
  decide +kernel

theorem iv246_c2 : below iv246.lo (caseIII1Q (lookDT treeK) admPre strsAll iv246.hi (iv246.p.getD 2 dPrm) (iv246.d.getD 2 [])) = true := by
  decide +kernel

theorem iv246_c3 : below iv246.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv246.hi (iv246.p.getD 3 dPrm) (iv246.d.getD 3 [])) = true := by
  decide +kernel

theorem iv246_c4 : below iv246.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv246.hi (iv246.p.getD 4 dPrm) (iv246.d.getD 4 []) (iv246.d.getD 5 [])) = true := by
  decide +kernel

theorem iv246_ok : checkIv2 (lookDT treeK) admPre strsAll iv246 = true :=
  checkIv2_of_cases _ _ _ iv246 rfl rfl (by decide +kernel) iv246_c0 iv246_c1 iv246_c2 iv246_c3 iv246_c4

end ErdosComp
