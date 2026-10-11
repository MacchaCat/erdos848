import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv131_c0 : below iv131.lo (caseIbQ (lookDT treeK) strsAll iv131.hi (iv131.p.getD 0 dPrm) (iv131.d.getD 0 [])) = true := by
  decide +kernel

theorem iv131_c1 : below iv131.lo (caseIIQ (lookDT treeK) admPre strsAll iv131.hi (iv131.p.getD 1 dPrm) (iv131.d.getD 1 [])) = true := by
  decide +kernel

theorem iv131_c2 : below iv131.lo (caseIII1Q (lookDT treeK) admPre strsAll iv131.hi (iv131.p.getD 2 dPrm) (iv131.d.getD 2 [])) = true := by
  decide +kernel

theorem iv131_c3 : below iv131.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv131.hi (iv131.p.getD 3 dPrm) (iv131.d.getD 3 [])) = true := by
  decide +kernel

theorem iv131_c4 : below iv131.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv131.hi (iv131.p.getD 4 dPrm) (iv131.d.getD 4 []) (iv131.d.getD 5 [])) = true := by
  decide +kernel

theorem iv131_ok : checkIv2 (lookDT treeK) admPre strsAll iv131 = true :=
  checkIv2_of_cases _ _ _ iv131 rfl rfl (by decide +kernel) iv131_c0 iv131_c1 iv131_c2 iv131_c3 iv131_c4

end ErdosComp
