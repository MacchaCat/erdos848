import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv13_c0 : below iv13.lo (caseIbQ (lookDT treeK) strsAll iv13.hi (iv13.p.getD 0 dPrm) (iv13.d.getD 0 [])) = true := by
  decide +kernel

theorem iv13_c1 : below iv13.lo (caseIIQ (lookDT treeK) admPre strsAll iv13.hi (iv13.p.getD 1 dPrm) (iv13.d.getD 1 [])) = true := by
  decide +kernel

theorem iv13_c2 : below iv13.lo (caseIII1Q (lookDT treeK) admPre strsAll iv13.hi (iv13.p.getD 2 dPrm) (iv13.d.getD 2 [])) = true := by
  decide +kernel

theorem iv13_c3 : below iv13.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv13.hi (iv13.p.getD 3 dPrm) (iv13.d.getD 3 [])) = true := by
  decide +kernel

theorem iv13_c4 : below iv13.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv13.hi (iv13.p.getD 4 dPrm) (iv13.d.getD 4 []) (iv13.d.getD 5 [])) = true := by
  decide +kernel

theorem iv13_ok : checkIv2 (lookDT treeK) admPre strsAll iv13 = true :=
  checkIv2_of_cases _ _ _ iv13 rfl rfl (by decide +kernel) iv13_c0 iv13_c1 iv13_c2 iv13_c3 iv13_c4

end ErdosComp
