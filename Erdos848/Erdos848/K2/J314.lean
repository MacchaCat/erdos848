import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv314_c0 : below iv314.lo (caseIbQ (lookDT treeK) strsAll iv314.hi (iv314.p.getD 0 dPrm) (iv314.d.getD 0 [])) = true := by
  decide +kernel

theorem iv314_c1 : below iv314.lo (caseIIQ (lookDT treeK) admPre strsAll iv314.hi (iv314.p.getD 1 dPrm) (iv314.d.getD 1 [])) = true := by
  decide +kernel

theorem iv314_c2 : below iv314.lo (caseIII1Q (lookDT treeK) admPre strsAll iv314.hi (iv314.p.getD 2 dPrm) (iv314.d.getD 2 [])) = true := by
  decide +kernel

theorem iv314_c3 : below iv314.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv314.hi (iv314.p.getD 3 dPrm) (iv314.d.getD 3 [])) = true := by
  decide +kernel

theorem iv314_c4 : below iv314.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv314.hi (iv314.p.getD 4 dPrm) (iv314.d.getD 4 []) (iv314.d.getD 5 [])) = true := by
  decide +kernel

theorem iv314_ok : checkIv2 (lookDT treeK) admPre strsAll iv314 = true :=
  checkIv2_of_cases _ _ _ iv314 rfl rfl (by decide +kernel) iv314_c0 iv314_c1 iv314_c2 iv314_c3 iv314_c4

end ErdosComp
