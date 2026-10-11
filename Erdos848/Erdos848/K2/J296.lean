import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv296_c0 : below iv296.lo (caseIbQ (lookDT treeK) strsAll iv296.hi (iv296.p.getD 0 dPrm) (iv296.d.getD 0 [])) = true := by
  decide +kernel

theorem iv296_c1 : below iv296.lo (caseIIQ (lookDT treeK) admPre strsAll iv296.hi (iv296.p.getD 1 dPrm) (iv296.d.getD 1 [])) = true := by
  decide +kernel

theorem iv296_c2 : below iv296.lo (caseIII1Q (lookDT treeK) admPre strsAll iv296.hi (iv296.p.getD 2 dPrm) (iv296.d.getD 2 [])) = true := by
  decide +kernel

theorem iv296_c3 : below iv296.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv296.hi (iv296.p.getD 3 dPrm) (iv296.d.getD 3 [])) = true := by
  decide +kernel

theorem iv296_c4 : below iv296.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv296.hi (iv296.p.getD 4 dPrm) (iv296.d.getD 4 []) (iv296.d.getD 5 [])) = true := by
  decide +kernel

theorem iv296_ok : checkIv2 (lookDT treeK) admPre strsAll iv296 = true :=
  checkIv2_of_cases _ _ _ iv296 rfl rfl (by decide +kernel) iv296_c0 iv296_c1 iv296_c2 iv296_c3 iv296_c4

end ErdosComp
