import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv120_c0 : below iv120.lo (caseIbQ (lookDT treeK) strsAll iv120.hi (iv120.p.getD 0 dPrm) (iv120.d.getD 0 [])) = true := by
  decide +kernel

theorem iv120_c1 : below iv120.lo (caseIIQ (lookDT treeK) admPre strsAll iv120.hi (iv120.p.getD 1 dPrm) (iv120.d.getD 1 [])) = true := by
  decide +kernel

theorem iv120_c2 : below iv120.lo (caseIII1Q (lookDT treeK) admPre strsAll iv120.hi (iv120.p.getD 2 dPrm) (iv120.d.getD 2 [])) = true := by
  decide +kernel

theorem iv120_c3 : below iv120.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv120.hi (iv120.p.getD 3 dPrm) (iv120.d.getD 3 [])) = true := by
  decide +kernel

theorem iv120_c4 : below iv120.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv120.hi (iv120.p.getD 4 dPrm) (iv120.d.getD 4 []) (iv120.d.getD 5 [])) = true := by
  decide +kernel

theorem iv120_ok : checkIv2 (lookDT treeK) admPre strsAll iv120 = true :=
  checkIv2_of_cases _ _ _ iv120 rfl rfl (by decide +kernel) iv120_c0 iv120_c1 iv120_c2 iv120_c3 iv120_c4

end ErdosComp
