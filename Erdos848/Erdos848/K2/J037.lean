import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv37_c0 : below iv37.lo (caseIbQ (lookDT treeK) strsAll iv37.hi (iv37.p.getD 0 dPrm) (iv37.d.getD 0 [])) = true := by
  decide +kernel

theorem iv37_c1 : below iv37.lo (caseIIQ (lookDT treeK) admPre strsAll iv37.hi (iv37.p.getD 1 dPrm) (iv37.d.getD 1 [])) = true := by
  decide +kernel

theorem iv37_c2 : below iv37.lo (caseIII1Q (lookDT treeK) admPre strsAll iv37.hi (iv37.p.getD 2 dPrm) (iv37.d.getD 2 [])) = true := by
  decide +kernel

theorem iv37_c3 : below iv37.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv37.hi (iv37.p.getD 3 dPrm) (iv37.d.getD 3 [])) = true := by
  decide +kernel

theorem iv37_c4 : below iv37.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv37.hi (iv37.p.getD 4 dPrm) (iv37.d.getD 4 []) (iv37.d.getD 5 [])) = true := by
  decide +kernel

theorem iv37_ok : checkIv2 (lookDT treeK) admPre strsAll iv37 = true :=
  checkIv2_of_cases _ _ _ iv37 rfl rfl (by decide +kernel) iv37_c0 iv37_c1 iv37_c2 iv37_c3 iv37_c4

end ErdosComp
