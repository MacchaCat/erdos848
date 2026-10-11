import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv18_c0 : below iv18.lo (caseIbQ (lookDT treeK) strsAll iv18.hi (iv18.p.getD 0 dPrm) (iv18.d.getD 0 [])) = true := by
  decide +kernel

theorem iv18_c1 : below iv18.lo (caseIIQ (lookDT treeK) admPre strsAll iv18.hi (iv18.p.getD 1 dPrm) (iv18.d.getD 1 [])) = true := by
  decide +kernel

theorem iv18_c2 : below iv18.lo (caseIII1Q (lookDT treeK) admPre strsAll iv18.hi (iv18.p.getD 2 dPrm) (iv18.d.getD 2 [])) = true := by
  decide +kernel

theorem iv18_c3 : below iv18.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv18.hi (iv18.p.getD 3 dPrm) (iv18.d.getD 3 [])) = true := by
  decide +kernel

theorem iv18_c4 : below iv18.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv18.hi (iv18.p.getD 4 dPrm) (iv18.d.getD 4 []) (iv18.d.getD 5 [])) = true := by
  decide +kernel

theorem iv18_ok : checkIv2 (lookDT treeK) admPre strsAll iv18 = true :=
  checkIv2_of_cases _ _ _ iv18 rfl rfl (by decide +kernel) iv18_c0 iv18_c1 iv18_c2 iv18_c3 iv18_c4

end ErdosComp
