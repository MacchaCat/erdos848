import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv107_c0 : below iv107.lo (caseIbQ (lookDT treeK) strsAll iv107.hi (iv107.p.getD 0 dPrm) (iv107.d.getD 0 [])) = true := by
  decide +kernel

theorem iv107_c1 : below iv107.lo (caseIIQ (lookDT treeK) admPre strsAll iv107.hi (iv107.p.getD 1 dPrm) (iv107.d.getD 1 [])) = true := by
  decide +kernel

theorem iv107_c2 : below iv107.lo (caseIII1Q (lookDT treeK) admPre strsAll iv107.hi (iv107.p.getD 2 dPrm) (iv107.d.getD 2 [])) = true := by
  decide +kernel

theorem iv107_c3 : below iv107.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv107.hi (iv107.p.getD 3 dPrm) (iv107.d.getD 3 [])) = true := by
  decide +kernel

theorem iv107_c4 : below iv107.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv107.hi (iv107.p.getD 4 dPrm) (iv107.d.getD 4 []) (iv107.d.getD 5 [])) = true := by
  decide +kernel

theorem iv107_ok : checkIv2 (lookDT treeK) admPre strsAll iv107 = true :=
  checkIv2_of_cases _ _ _ iv107 rfl rfl (by decide +kernel) iv107_c0 iv107_c1 iv107_c2 iv107_c3 iv107_c4

end ErdosComp
