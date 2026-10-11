import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv15_c0 : below iv15.lo (caseIbQ (lookDT treeK) strsAll iv15.hi (iv15.p.getD 0 dPrm) (iv15.d.getD 0 [])) = true := by
  decide +kernel

theorem iv15_c1 : below iv15.lo (caseIIQ (lookDT treeK) admPre strsAll iv15.hi (iv15.p.getD 1 dPrm) (iv15.d.getD 1 [])) = true := by
  decide +kernel

theorem iv15_c2 : below iv15.lo (caseIII1Q (lookDT treeK) admPre strsAll iv15.hi (iv15.p.getD 2 dPrm) (iv15.d.getD 2 [])) = true := by
  decide +kernel

theorem iv15_c3 : below iv15.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv15.hi (iv15.p.getD 3 dPrm) (iv15.d.getD 3 [])) = true := by
  decide +kernel

theorem iv15_c4 : below iv15.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv15.hi (iv15.p.getD 4 dPrm) (iv15.d.getD 4 []) (iv15.d.getD 5 [])) = true := by
  decide +kernel

theorem iv15_ok : checkIv2 (lookDT treeK) admPre strsAll iv15 = true :=
  checkIv2_of_cases _ _ _ iv15 rfl rfl (by decide +kernel) iv15_c0 iv15_c1 iv15_c2 iv15_c3 iv15_c4

end ErdosComp
