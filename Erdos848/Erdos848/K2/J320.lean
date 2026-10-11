import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv320_c0 : below iv320.lo (caseIbQ (lookDT treeK) strsAll iv320.hi (iv320.p.getD 0 dPrm) (iv320.d.getD 0 [])) = true := by
  decide +kernel

theorem iv320_c1 : below iv320.lo (caseIIQ (lookDT treeK) admPre strsAll iv320.hi (iv320.p.getD 1 dPrm) (iv320.d.getD 1 [])) = true := by
  decide +kernel

theorem iv320_c2 : below iv320.lo (caseIII1Q (lookDT treeK) admPre strsAll iv320.hi (iv320.p.getD 2 dPrm) (iv320.d.getD 2 [])) = true := by
  decide +kernel

theorem iv320_c3 : below iv320.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv320.hi (iv320.p.getD 3 dPrm) (iv320.d.getD 3 [])) = true := by
  decide +kernel

theorem iv320_c4 : below iv320.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv320.hi (iv320.p.getD 4 dPrm) (iv320.d.getD 4 []) (iv320.d.getD 5 [])) = true := by
  decide +kernel

theorem iv320_ok : checkIv2 (lookDT treeK) admPre strsAll iv320 = true :=
  checkIv2_of_cases _ _ _ iv320 rfl rfl (by decide +kernel) iv320_c0 iv320_c1 iv320_c2 iv320_c3 iv320_c4

end ErdosComp
