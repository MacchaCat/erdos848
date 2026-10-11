import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv307_c0 : below iv307.lo (caseIbQ (lookDT treeK) strsAll iv307.hi (iv307.p.getD 0 dPrm) (iv307.d.getD 0 [])) = true := by
  decide +kernel

theorem iv307_c1 : below iv307.lo (caseIIQ (lookDT treeK) admPre strsAll iv307.hi (iv307.p.getD 1 dPrm) (iv307.d.getD 1 [])) = true := by
  decide +kernel

theorem iv307_c2 : below iv307.lo (caseIII1Q (lookDT treeK) admPre strsAll iv307.hi (iv307.p.getD 2 dPrm) (iv307.d.getD 2 [])) = true := by
  decide +kernel

theorem iv307_c3 : below iv307.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv307.hi (iv307.p.getD 3 dPrm) (iv307.d.getD 3 [])) = true := by
  decide +kernel

theorem iv307_c4 : below iv307.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv307.hi (iv307.p.getD 4 dPrm) (iv307.d.getD 4 []) (iv307.d.getD 5 [])) = true := by
  decide +kernel

theorem iv307_ok : checkIv2 (lookDT treeK) admPre strsAll iv307 = true :=
  checkIv2_of_cases _ _ _ iv307 rfl rfl (by decide +kernel) iv307_c0 iv307_c1 iv307_c2 iv307_c3 iv307_c4

end ErdosComp
