import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv288_c0 : below iv288.lo (caseIbQ (lookDT treeK) strsAll iv288.hi (iv288.p.getD 0 dPrm) (iv288.d.getD 0 [])) = true := by
  decide +kernel

theorem iv288_c1 : below iv288.lo (caseIIQ (lookDT treeK) admPre strsAll iv288.hi (iv288.p.getD 1 dPrm) (iv288.d.getD 1 [])) = true := by
  decide +kernel

theorem iv288_c2 : below iv288.lo (caseIII1Q (lookDT treeK) admPre strsAll iv288.hi (iv288.p.getD 2 dPrm) (iv288.d.getD 2 [])) = true := by
  decide +kernel

theorem iv288_c3 : below iv288.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv288.hi (iv288.p.getD 3 dPrm) (iv288.d.getD 3 [])) = true := by
  decide +kernel

theorem iv288_c4 : below iv288.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv288.hi (iv288.p.getD 4 dPrm) (iv288.d.getD 4 []) (iv288.d.getD 5 [])) = true := by
  decide +kernel

theorem iv288_ok : checkIv2 (lookDT treeK) admPre strsAll iv288 = true :=
  checkIv2_of_cases _ _ _ iv288 rfl rfl (by decide +kernel) iv288_c0 iv288_c1 iv288_c2 iv288_c3 iv288_c4

end ErdosComp
