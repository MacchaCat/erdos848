import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv73_c0 : below iv73.lo (caseIbQ (lookDT treeK) strsAll iv73.hi (iv73.p.getD 0 dPrm) (iv73.d.getD 0 [])) = true := by
  decide +kernel

theorem iv73_c1 : below iv73.lo (caseIIQ (lookDT treeK) admPre strsAll iv73.hi (iv73.p.getD 1 dPrm) (iv73.d.getD 1 [])) = true := by
  decide +kernel

theorem iv73_c2 : below iv73.lo (caseIII1Q (lookDT treeK) admPre strsAll iv73.hi (iv73.p.getD 2 dPrm) (iv73.d.getD 2 [])) = true := by
  decide +kernel

theorem iv73_c3 : below iv73.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv73.hi (iv73.p.getD 3 dPrm) (iv73.d.getD 3 [])) = true := by
  decide +kernel

theorem iv73_c4 : below iv73.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv73.hi (iv73.p.getD 4 dPrm) (iv73.d.getD 4 []) (iv73.d.getD 5 [])) = true := by
  decide +kernel

theorem iv73_ok : checkIv2 (lookDT treeK) admPre strsAll iv73 = true :=
  checkIv2_of_cases _ _ _ iv73 rfl rfl (by decide +kernel) iv73_c0 iv73_c1 iv73_c2 iv73_c3 iv73_c4

end ErdosComp
