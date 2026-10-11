import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv17_c0 : below iv17.lo (caseIbQ (lookDT treeK) strsAll iv17.hi (iv17.p.getD 0 dPrm) (iv17.d.getD 0 [])) = true := by
  decide +kernel

theorem iv17_c1 : below iv17.lo (caseIIQ (lookDT treeK) admPre strsAll iv17.hi (iv17.p.getD 1 dPrm) (iv17.d.getD 1 [])) = true := by
  decide +kernel

theorem iv17_c2 : below iv17.lo (caseIII1Q (lookDT treeK) admPre strsAll iv17.hi (iv17.p.getD 2 dPrm) (iv17.d.getD 2 [])) = true := by
  decide +kernel

theorem iv17_c3 : below iv17.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv17.hi (iv17.p.getD 3 dPrm) (iv17.d.getD 3 [])) = true := by
  decide +kernel

theorem iv17_c4 : below iv17.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv17.hi (iv17.p.getD 4 dPrm) (iv17.d.getD 4 []) (iv17.d.getD 5 [])) = true := by
  decide +kernel

theorem iv17_ok : checkIv2 (lookDT treeK) admPre strsAll iv17 = true :=
  checkIv2_of_cases _ _ _ iv17 rfl rfl (by decide +kernel) iv17_c0 iv17_c1 iv17_c2 iv17_c3 iv17_c4

end ErdosComp
