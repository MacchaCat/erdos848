import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv5_c0 : below iv5.lo (caseIbQ (lookDT treeK) strsAll iv5.hi (iv5.p.getD 0 dPrm) (iv5.d.getD 0 [])) = true := by
  decide +kernel

theorem iv5_c1 : below iv5.lo (caseIIQ (lookDT treeK) admPre strsAll iv5.hi (iv5.p.getD 1 dPrm) (iv5.d.getD 1 [])) = true := by
  decide +kernel

theorem iv5_c2 : below iv5.lo (caseIII1Q (lookDT treeK) admPre strsAll iv5.hi (iv5.p.getD 2 dPrm) (iv5.d.getD 2 [])) = true := by
  decide +kernel

theorem iv5_c3 : below iv5.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv5.hi (iv5.p.getD 3 dPrm) (iv5.d.getD 3 [])) = true := by
  decide +kernel

theorem iv5_c4 : below iv5.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv5.hi (iv5.p.getD 4 dPrm) (iv5.d.getD 4 []) (iv5.d.getD 5 [])) = true := by
  decide +kernel

theorem iv5_ok : checkIv2 (lookDT treeK) admPre strsAll iv5 = true :=
  checkIv2_of_cases _ _ _ iv5 rfl rfl (by decide +kernel) iv5_c0 iv5_c1 iv5_c2 iv5_c3 iv5_c4

end ErdosComp
