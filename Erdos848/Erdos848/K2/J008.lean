import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv8_c0 : below iv8.lo (caseIbQ (lookDT treeK) strsAll iv8.hi (iv8.p.getD 0 dPrm) (iv8.d.getD 0 [])) = true := by
  decide +kernel

theorem iv8_c1 : below iv8.lo (caseIIQ (lookDT treeK) admPre strsAll iv8.hi (iv8.p.getD 1 dPrm) (iv8.d.getD 1 [])) = true := by
  decide +kernel

theorem iv8_c2 : below iv8.lo (caseIII1Q (lookDT treeK) admPre strsAll iv8.hi (iv8.p.getD 2 dPrm) (iv8.d.getD 2 [])) = true := by
  decide +kernel

theorem iv8_c3 : below iv8.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv8.hi (iv8.p.getD 3 dPrm) (iv8.d.getD 3 [])) = true := by
  decide +kernel

theorem iv8_c4 : below iv8.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv8.hi (iv8.p.getD 4 dPrm) (iv8.d.getD 4 []) (iv8.d.getD 5 [])) = true := by
  decide +kernel

theorem iv8_ok : checkIv2 (lookDT treeK) admPre strsAll iv8 = true :=
  checkIv2_of_cases _ _ _ iv8 rfl rfl (by decide +kernel) iv8_c0 iv8_c1 iv8_c2 iv8_c3 iv8_c4

end ErdosComp
