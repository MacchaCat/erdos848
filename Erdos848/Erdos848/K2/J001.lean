import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv1_c0 : below iv1.lo (caseIbQ (lookDT treeK) strsAll iv1.hi (iv1.p.getD 0 dPrm) (iv1.d.getD 0 [])) = true := by
  decide +kernel

theorem iv1_c1 : below iv1.lo (caseIIQ (lookDT treeK) admPre strsAll iv1.hi (iv1.p.getD 1 dPrm) (iv1.d.getD 1 [])) = true := by
  decide +kernel

theorem iv1_c2 : below iv1.lo (caseIII1Q (lookDT treeK) admPre strsAll iv1.hi (iv1.p.getD 2 dPrm) (iv1.d.getD 2 [])) = true := by
  decide +kernel

theorem iv1_c3 : below iv1.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv1.hi (iv1.p.getD 3 dPrm) (iv1.d.getD 3 [])) = true := by
  decide +kernel

theorem iv1_c4 : below iv1.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv1.hi (iv1.p.getD 4 dPrm) (iv1.d.getD 4 []) (iv1.d.getD 5 [])) = true := by
  decide +kernel

theorem iv1_ok : checkIv2 (lookDT treeK) admPre strsAll iv1 = true :=
  checkIv2_of_cases _ _ _ iv1 rfl rfl (by decide +kernel) iv1_c0 iv1_c1 iv1_c2 iv1_c3 iv1_c4

end ErdosComp
