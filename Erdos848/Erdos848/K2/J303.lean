import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv303_c0 : below iv303.lo (caseIbQ (lookDT treeK) strsAll iv303.hi (iv303.p.getD 0 dPrm) (iv303.d.getD 0 [])) = true := by
  decide +kernel

theorem iv303_c1 : below iv303.lo (caseIIQ (lookDT treeK) admPre strsAll iv303.hi (iv303.p.getD 1 dPrm) (iv303.d.getD 1 [])) = true := by
  decide +kernel

theorem iv303_c2 : below iv303.lo (caseIII1Q (lookDT treeK) admPre strsAll iv303.hi (iv303.p.getD 2 dPrm) (iv303.d.getD 2 [])) = true := by
  decide +kernel

theorem iv303_c3 : below iv303.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv303.hi (iv303.p.getD 3 dPrm) (iv303.d.getD 3 [])) = true := by
  decide +kernel

theorem iv303_c4 : below iv303.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv303.hi (iv303.p.getD 4 dPrm) (iv303.d.getD 4 []) (iv303.d.getD 5 [])) = true := by
  decide +kernel

theorem iv303_ok : checkIv2 (lookDT treeK) admPre strsAll iv303 = true :=
  checkIv2_of_cases _ _ _ iv303 rfl rfl (by decide +kernel) iv303_c0 iv303_c1 iv303_c2 iv303_c3 iv303_c4

end ErdosComp
