import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv240_c0 : below iv240.lo (caseIbQ (lookDT treeK) strsAll iv240.hi (iv240.p.getD 0 dPrm) (iv240.d.getD 0 [])) = true := by
  decide +kernel

theorem iv240_c1 : below iv240.lo (caseIIQ (lookDT treeK) admPre strsAll iv240.hi (iv240.p.getD 1 dPrm) (iv240.d.getD 1 [])) = true := by
  decide +kernel

theorem iv240_c2 : below iv240.lo (caseIII1Q (lookDT treeK) admPre strsAll iv240.hi (iv240.p.getD 2 dPrm) (iv240.d.getD 2 [])) = true := by
  decide +kernel

theorem iv240_c3 : below iv240.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv240.hi (iv240.p.getD 3 dPrm) (iv240.d.getD 3 [])) = true := by
  decide +kernel

theorem iv240_c4 : below iv240.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv240.hi (iv240.p.getD 4 dPrm) (iv240.d.getD 4 []) (iv240.d.getD 5 [])) = true := by
  decide +kernel

theorem iv240_ok : checkIv2 (lookDT treeK) admPre strsAll iv240 = true :=
  checkIv2_of_cases _ _ _ iv240 rfl rfl (by decide +kernel) iv240_c0 iv240_c1 iv240_c2 iv240_c3 iv240_c4

end ErdosComp
