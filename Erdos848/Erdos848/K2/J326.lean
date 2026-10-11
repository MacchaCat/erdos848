import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv326_c0 : below iv326.lo (caseIbQ (lookDT treeK) strsAll iv326.hi (iv326.p.getD 0 dPrm) (iv326.d.getD 0 [])) = true := by
  decide +kernel

theorem iv326_c1 : below iv326.lo (caseIIQ (lookDT treeK) admPre strsAll iv326.hi (iv326.p.getD 1 dPrm) (iv326.d.getD 1 [])) = true := by
  decide +kernel

theorem iv326_c2 : below iv326.lo (caseIII1Q (lookDT treeK) admPre strsAll iv326.hi (iv326.p.getD 2 dPrm) (iv326.d.getD 2 [])) = true := by
  decide +kernel

theorem iv326_c3 : below iv326.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv326.hi (iv326.p.getD 3 dPrm) (iv326.d.getD 3 [])) = true := by
  decide +kernel

theorem iv326_c4 : below iv326.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv326.hi (iv326.p.getD 4 dPrm) (iv326.d.getD 4 []) (iv326.d.getD 5 [])) = true := by
  decide +kernel

theorem iv326_ok : checkIv2 (lookDT treeK) admPre strsAll iv326 = true :=
  checkIv2_of_cases _ _ _ iv326 rfl rfl (by decide +kernel) iv326_c0 iv326_c1 iv326_c2 iv326_c3 iv326_c4

end ErdosComp
