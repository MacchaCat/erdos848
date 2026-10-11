import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv6_c0 : below iv6.lo (caseIbQ (lookDT treeK) strsAll iv6.hi (iv6.p.getD 0 dPrm) (iv6.d.getD 0 [])) = true := by
  decide +kernel

theorem iv6_c1 : below iv6.lo (caseIIQ (lookDT treeK) admPre strsAll iv6.hi (iv6.p.getD 1 dPrm) (iv6.d.getD 1 [])) = true := by
  decide +kernel

theorem iv6_c2 : below iv6.lo (caseIII1Q (lookDT treeK) admPre strsAll iv6.hi (iv6.p.getD 2 dPrm) (iv6.d.getD 2 [])) = true := by
  decide +kernel

theorem iv6_c3 : below iv6.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv6.hi (iv6.p.getD 3 dPrm) (iv6.d.getD 3 [])) = true := by
  decide +kernel

theorem iv6_c4 : below iv6.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv6.hi (iv6.p.getD 4 dPrm) (iv6.d.getD 4 []) (iv6.d.getD 5 [])) = true := by
  decide +kernel

theorem iv6_ok : checkIv2 (lookDT treeK) admPre strsAll iv6 = true :=
  checkIv2_of_cases _ _ _ iv6 rfl rfl (by decide +kernel) iv6_c0 iv6_c1 iv6_c2 iv6_c3 iv6_c4

end ErdosComp
