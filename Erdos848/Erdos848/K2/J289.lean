import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv289_c0 : below iv289.lo (caseIbQ (lookDT treeK) strsAll iv289.hi (iv289.p.getD 0 dPrm) (iv289.d.getD 0 [])) = true := by
  decide +kernel

theorem iv289_c1 : below iv289.lo (caseIIQ (lookDT treeK) admPre strsAll iv289.hi (iv289.p.getD 1 dPrm) (iv289.d.getD 1 [])) = true := by
  decide +kernel

theorem iv289_c2 : below iv289.lo (caseIII1Q (lookDT treeK) admPre strsAll iv289.hi (iv289.p.getD 2 dPrm) (iv289.d.getD 2 [])) = true := by
  decide +kernel

theorem iv289_c3 : below iv289.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv289.hi (iv289.p.getD 3 dPrm) (iv289.d.getD 3 [])) = true := by
  decide +kernel

theorem iv289_c4 : below iv289.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv289.hi (iv289.p.getD 4 dPrm) (iv289.d.getD 4 []) (iv289.d.getD 5 [])) = true := by
  decide +kernel

theorem iv289_ok : checkIv2 (lookDT treeK) admPre strsAll iv289 = true :=
  checkIv2_of_cases _ _ _ iv289 rfl rfl (by decide +kernel) iv289_c0 iv289_c1 iv289_c2 iv289_c3 iv289_c4

end ErdosComp
