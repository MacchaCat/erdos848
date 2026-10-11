import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv250_c0 : below iv250.lo (caseIbQ (lookDT treeK) strsAll iv250.hi (iv250.p.getD 0 dPrm) (iv250.d.getD 0 [])) = true := by
  decide +kernel

theorem iv250_c1 : below iv250.lo (caseIIQ (lookDT treeK) admPre strsAll iv250.hi (iv250.p.getD 1 dPrm) (iv250.d.getD 1 [])) = true := by
  decide +kernel

theorem iv250_c2 : below iv250.lo (caseIII1Q (lookDT treeK) admPre strsAll iv250.hi (iv250.p.getD 2 dPrm) (iv250.d.getD 2 [])) = true := by
  decide +kernel

theorem iv250_c3 : below iv250.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv250.hi (iv250.p.getD 3 dPrm) (iv250.d.getD 3 [])) = true := by
  decide +kernel

theorem iv250_c4 : below iv250.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv250.hi (iv250.p.getD 4 dPrm) (iv250.d.getD 4 []) (iv250.d.getD 5 [])) = true := by
  decide +kernel

theorem iv250_ok : checkIv2 (lookDT treeK) admPre strsAll iv250 = true :=
  checkIv2_of_cases _ _ _ iv250 rfl rfl (by decide +kernel) iv250_c0 iv250_c1 iv250_c2 iv250_c3 iv250_c4

end ErdosComp
