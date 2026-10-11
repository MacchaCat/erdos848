import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv43_c0 : below iv43.lo (caseIbQ (lookDT treeK) strsAll iv43.hi (iv43.p.getD 0 dPrm) (iv43.d.getD 0 [])) = true := by
  decide +kernel

theorem iv43_c1 : below iv43.lo (caseIIQ (lookDT treeK) admPre strsAll iv43.hi (iv43.p.getD 1 dPrm) (iv43.d.getD 1 [])) = true := by
  decide +kernel

theorem iv43_c2 : below iv43.lo (caseIII1Q (lookDT treeK) admPre strsAll iv43.hi (iv43.p.getD 2 dPrm) (iv43.d.getD 2 [])) = true := by
  decide +kernel

theorem iv43_c3 : below iv43.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv43.hi (iv43.p.getD 3 dPrm) (iv43.d.getD 3 [])) = true := by
  decide +kernel

theorem iv43_c4 : below iv43.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv43.hi (iv43.p.getD 4 dPrm) (iv43.d.getD 4 []) (iv43.d.getD 5 [])) = true := by
  decide +kernel

theorem iv43_ok : checkIv2 (lookDT treeK) admPre strsAll iv43 = true :=
  checkIv2_of_cases _ _ _ iv43 rfl rfl (by decide +kernel) iv43_c0 iv43_c1 iv43_c2 iv43_c3 iv43_c4

end ErdosComp
