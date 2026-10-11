import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv191_c0 : below iv191.lo (caseIbQ (lookDT treeK) strsAll iv191.hi (iv191.p.getD 0 dPrm) (iv191.d.getD 0 [])) = true := by
  decide +kernel

theorem iv191_c1 : below iv191.lo (caseIIQ (lookDT treeK) admPre strsAll iv191.hi (iv191.p.getD 1 dPrm) (iv191.d.getD 1 [])) = true := by
  decide +kernel

theorem iv191_c2 : below iv191.lo (caseIII1Q (lookDT treeK) admPre strsAll iv191.hi (iv191.p.getD 2 dPrm) (iv191.d.getD 2 [])) = true := by
  decide +kernel

theorem iv191_c3 : below iv191.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv191.hi (iv191.p.getD 3 dPrm) (iv191.d.getD 3 [])) = true := by
  decide +kernel

theorem iv191_c4 : below iv191.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv191.hi (iv191.p.getD 4 dPrm) (iv191.d.getD 4 []) (iv191.d.getD 5 [])) = true := by
  decide +kernel

theorem iv191_ok : checkIv2 (lookDT treeK) admPre strsAll iv191 = true :=
  checkIv2_of_cases _ _ _ iv191 rfl rfl (by decide +kernel) iv191_c0 iv191_c1 iv191_c2 iv191_c3 iv191_c4

end ErdosComp
