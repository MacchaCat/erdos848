import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv84_c0 : below iv84.lo (caseIbQ (lookDT treeK) strsAll iv84.hi (iv84.p.getD 0 dPrm) (iv84.d.getD 0 [])) = true := by
  decide +kernel

theorem iv84_c1 : below iv84.lo (caseIIQ (lookDT treeK) admPre strsAll iv84.hi (iv84.p.getD 1 dPrm) (iv84.d.getD 1 [])) = true := by
  decide +kernel

theorem iv84_c2 : below iv84.lo (caseIII1Q (lookDT treeK) admPre strsAll iv84.hi (iv84.p.getD 2 dPrm) (iv84.d.getD 2 [])) = true := by
  decide +kernel

theorem iv84_c3 : below iv84.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv84.hi (iv84.p.getD 3 dPrm) (iv84.d.getD 3 [])) = true := by
  decide +kernel

theorem iv84_c4 : below iv84.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv84.hi (iv84.p.getD 4 dPrm) (iv84.d.getD 4 []) (iv84.d.getD 5 [])) = true := by
  decide +kernel

theorem iv84_ok : checkIv2 (lookDT treeK) admPre strsAll iv84 = true :=
  checkIv2_of_cases _ _ _ iv84 rfl rfl (by decide +kernel) iv84_c0 iv84_c1 iv84_c2 iv84_c3 iv84_c4

end ErdosComp
