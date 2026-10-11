import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv329_c0 : below iv329.lo (caseIbQ (lookDT treeK) strsAll iv329.hi (iv329.p.getD 0 dPrm) (iv329.d.getD 0 [])) = true := by
  decide +kernel

theorem iv329_c1 : below iv329.lo (caseIIQ (lookDT treeK) admPre strsAll iv329.hi (iv329.p.getD 1 dPrm) (iv329.d.getD 1 [])) = true := by
  decide +kernel

theorem iv329_c2 : below iv329.lo (caseIII1Q (lookDT treeK) admPre strsAll iv329.hi (iv329.p.getD 2 dPrm) (iv329.d.getD 2 [])) = true := by
  decide +kernel

theorem iv329_c3 : below iv329.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv329.hi (iv329.p.getD 3 dPrm) (iv329.d.getD 3 [])) = true := by
  decide +kernel

theorem iv329_c4 : below iv329.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv329.hi (iv329.p.getD 4 dPrm) (iv329.d.getD 4 []) (iv329.d.getD 5 [])) = true := by
  decide +kernel

theorem iv329_ok : checkIv2 (lookDT treeK) admPre strsAll iv329 = true :=
  checkIv2_of_cases _ _ _ iv329 rfl rfl (by decide +kernel) iv329_c0 iv329_c1 iv329_c2 iv329_c3 iv329_c4

end ErdosComp
