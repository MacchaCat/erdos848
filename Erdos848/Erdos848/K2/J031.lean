import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv31_c0 : below iv31.lo (caseIbQ (lookDT treeK) strsAll iv31.hi (iv31.p.getD 0 dPrm) (iv31.d.getD 0 [])) = true := by
  decide +kernel

theorem iv31_c1 : below iv31.lo (caseIIQ (lookDT treeK) admPre strsAll iv31.hi (iv31.p.getD 1 dPrm) (iv31.d.getD 1 [])) = true := by
  decide +kernel

theorem iv31_c2 : below iv31.lo (caseIII1Q (lookDT treeK) admPre strsAll iv31.hi (iv31.p.getD 2 dPrm) (iv31.d.getD 2 [])) = true := by
  decide +kernel

theorem iv31_c3 : below iv31.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv31.hi (iv31.p.getD 3 dPrm) (iv31.d.getD 3 [])) = true := by
  decide +kernel

theorem iv31_c4 : below iv31.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv31.hi (iv31.p.getD 4 dPrm) (iv31.d.getD 4 []) (iv31.d.getD 5 [])) = true := by
  decide +kernel

theorem iv31_ok : checkIv2 (lookDT treeK) admPre strsAll iv31 = true :=
  checkIv2_of_cases _ _ _ iv31 rfl rfl (by decide +kernel) iv31_c0 iv31_c1 iv31_c2 iv31_c3 iv31_c4

end ErdosComp
