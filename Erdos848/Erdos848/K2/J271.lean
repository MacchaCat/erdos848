import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv271_c0 : below iv271.lo (caseIbQ (lookDT treeK) strsAll iv271.hi (iv271.p.getD 0 dPrm) (iv271.d.getD 0 [])) = true := by
  decide +kernel

theorem iv271_c1 : below iv271.lo (caseIIQ (lookDT treeK) admPre strsAll iv271.hi (iv271.p.getD 1 dPrm) (iv271.d.getD 1 [])) = true := by
  decide +kernel

theorem iv271_c2 : below iv271.lo (caseIII1Q (lookDT treeK) admPre strsAll iv271.hi (iv271.p.getD 2 dPrm) (iv271.d.getD 2 [])) = true := by
  decide +kernel

theorem iv271_c3 : below iv271.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv271.hi (iv271.p.getD 3 dPrm) (iv271.d.getD 3 [])) = true := by
  decide +kernel

theorem iv271_c4 : below iv271.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv271.hi (iv271.p.getD 4 dPrm) (iv271.d.getD 4 []) (iv271.d.getD 5 [])) = true := by
  decide +kernel

theorem iv271_ok : checkIv2 (lookDT treeK) admPre strsAll iv271 = true :=
  checkIv2_of_cases _ _ _ iv271 rfl rfl (by decide +kernel) iv271_c0 iv271_c1 iv271_c2 iv271_c3 iv271_c4

end ErdosComp
