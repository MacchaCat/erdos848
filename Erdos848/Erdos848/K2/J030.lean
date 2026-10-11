import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv30_c0 : below iv30.lo (caseIbQ (lookDT treeK) strsAll iv30.hi (iv30.p.getD 0 dPrm) (iv30.d.getD 0 [])) = true := by
  decide +kernel

theorem iv30_c1 : below iv30.lo (caseIIQ (lookDT treeK) admPre strsAll iv30.hi (iv30.p.getD 1 dPrm) (iv30.d.getD 1 [])) = true := by
  decide +kernel

theorem iv30_c2 : below iv30.lo (caseIII1Q (lookDT treeK) admPre strsAll iv30.hi (iv30.p.getD 2 dPrm) (iv30.d.getD 2 [])) = true := by
  decide +kernel

theorem iv30_c3 : below iv30.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv30.hi (iv30.p.getD 3 dPrm) (iv30.d.getD 3 [])) = true := by
  decide +kernel

theorem iv30_c4 : below iv30.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv30.hi (iv30.p.getD 4 dPrm) (iv30.d.getD 4 []) (iv30.d.getD 5 [])) = true := by
  decide +kernel

theorem iv30_ok : checkIv2 (lookDT treeK) admPre strsAll iv30 = true :=
  checkIv2_of_cases _ _ _ iv30 rfl rfl (by decide +kernel) iv30_c0 iv30_c1 iv30_c2 iv30_c3 iv30_c4

end ErdosComp
