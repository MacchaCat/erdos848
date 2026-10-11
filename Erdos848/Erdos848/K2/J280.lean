import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv280_c0 : below iv280.lo (caseIbQ (lookDT treeK) strsAll iv280.hi (iv280.p.getD 0 dPrm) (iv280.d.getD 0 [])) = true := by
  decide +kernel

theorem iv280_c1 : below iv280.lo (caseIIQ (lookDT treeK) admPre strsAll iv280.hi (iv280.p.getD 1 dPrm) (iv280.d.getD 1 [])) = true := by
  decide +kernel

theorem iv280_c2 : below iv280.lo (caseIII1Q (lookDT treeK) admPre strsAll iv280.hi (iv280.p.getD 2 dPrm) (iv280.d.getD 2 [])) = true := by
  decide +kernel

theorem iv280_c3 : below iv280.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv280.hi (iv280.p.getD 3 dPrm) (iv280.d.getD 3 [])) = true := by
  decide +kernel

theorem iv280_c4 : below iv280.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv280.hi (iv280.p.getD 4 dPrm) (iv280.d.getD 4 []) (iv280.d.getD 5 [])) = true := by
  decide +kernel

theorem iv280_ok : checkIv2 (lookDT treeK) admPre strsAll iv280 = true :=
  checkIv2_of_cases _ _ _ iv280 rfl rfl (by decide +kernel) iv280_c0 iv280_c1 iv280_c2 iv280_c3 iv280_c4

end ErdosComp
