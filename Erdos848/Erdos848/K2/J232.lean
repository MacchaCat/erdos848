import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv232_c0 : below iv232.lo (caseIbQ (lookDT treeK) strsAll iv232.hi (iv232.p.getD 0 dPrm) (iv232.d.getD 0 [])) = true := by
  decide +kernel

theorem iv232_c1 : below iv232.lo (caseIIQ (lookDT treeK) admPre strsAll iv232.hi (iv232.p.getD 1 dPrm) (iv232.d.getD 1 [])) = true := by
  decide +kernel

theorem iv232_c2 : below iv232.lo (caseIII1Q (lookDT treeK) admPre strsAll iv232.hi (iv232.p.getD 2 dPrm) (iv232.d.getD 2 [])) = true := by
  decide +kernel

theorem iv232_c3 : below iv232.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv232.hi (iv232.p.getD 3 dPrm) (iv232.d.getD 3 [])) = true := by
  decide +kernel

theorem iv232_c4 : below iv232.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv232.hi (iv232.p.getD 4 dPrm) (iv232.d.getD 4 []) (iv232.d.getD 5 [])) = true := by
  decide +kernel

theorem iv232_ok : checkIv2 (lookDT treeK) admPre strsAll iv232 = true :=
  checkIv2_of_cases _ _ _ iv232 rfl rfl (by decide +kernel) iv232_c0 iv232_c1 iv232_c2 iv232_c3 iv232_c4

end ErdosComp
