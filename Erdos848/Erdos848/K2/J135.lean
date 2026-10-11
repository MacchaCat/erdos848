import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv135_c0 : below iv135.lo (caseIbQ (lookDT treeK) strsAll iv135.hi (iv135.p.getD 0 dPrm) (iv135.d.getD 0 [])) = true := by
  decide +kernel

theorem iv135_c1 : below iv135.lo (caseIIQ (lookDT treeK) admPre strsAll iv135.hi (iv135.p.getD 1 dPrm) (iv135.d.getD 1 [])) = true := by
  decide +kernel

theorem iv135_c2 : below iv135.lo (caseIII1Q (lookDT treeK) admPre strsAll iv135.hi (iv135.p.getD 2 dPrm) (iv135.d.getD 2 [])) = true := by
  decide +kernel

theorem iv135_c3 : below iv135.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv135.hi (iv135.p.getD 3 dPrm) (iv135.d.getD 3 [])) = true := by
  decide +kernel

theorem iv135_c4 : below iv135.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv135.hi (iv135.p.getD 4 dPrm) (iv135.d.getD 4 []) (iv135.d.getD 5 [])) = true := by
  decide +kernel

theorem iv135_ok : checkIv2 (lookDT treeK) admPre strsAll iv135 = true :=
  checkIv2_of_cases _ _ _ iv135 rfl rfl (by decide +kernel) iv135_c0 iv135_c1 iv135_c2 iv135_c3 iv135_c4

end ErdosComp
