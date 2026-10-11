import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv78_c0 : below iv78.lo (caseIbQ (lookDT treeK) strsAll iv78.hi (iv78.p.getD 0 dPrm) (iv78.d.getD 0 [])) = true := by
  decide +kernel

theorem iv78_c1 : below iv78.lo (caseIIQ (lookDT treeK) admPre strsAll iv78.hi (iv78.p.getD 1 dPrm) (iv78.d.getD 1 [])) = true := by
  decide +kernel

theorem iv78_c2 : below iv78.lo (caseIII1Q (lookDT treeK) admPre strsAll iv78.hi (iv78.p.getD 2 dPrm) (iv78.d.getD 2 [])) = true := by
  decide +kernel

theorem iv78_c3 : below iv78.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv78.hi (iv78.p.getD 3 dPrm) (iv78.d.getD 3 [])) = true := by
  decide +kernel

theorem iv78_c4 : below iv78.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv78.hi (iv78.p.getD 4 dPrm) (iv78.d.getD 4 []) (iv78.d.getD 5 [])) = true := by
  decide +kernel

theorem iv78_ok : checkIv2 (lookDT treeK) admPre strsAll iv78 = true :=
  checkIv2_of_cases _ _ _ iv78 rfl rfl (by decide +kernel) iv78_c0 iv78_c1 iv78_c2 iv78_c3 iv78_c4

end ErdosComp
