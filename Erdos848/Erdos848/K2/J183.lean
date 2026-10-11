import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv183_c0 : below iv183.lo (caseIbQ (lookDT treeK) strsAll iv183.hi (iv183.p.getD 0 dPrm) (iv183.d.getD 0 [])) = true := by
  decide +kernel

theorem iv183_c1 : below iv183.lo (caseIIQ (lookDT treeK) admPre strsAll iv183.hi (iv183.p.getD 1 dPrm) (iv183.d.getD 1 [])) = true := by
  decide +kernel

theorem iv183_c2 : below iv183.lo (caseIII1Q (lookDT treeK) admPre strsAll iv183.hi (iv183.p.getD 2 dPrm) (iv183.d.getD 2 [])) = true := by
  decide +kernel

theorem iv183_c3 : below iv183.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv183.hi (iv183.p.getD 3 dPrm) (iv183.d.getD 3 [])) = true := by
  decide +kernel

theorem iv183_c4 : below iv183.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv183.hi (iv183.p.getD 4 dPrm) (iv183.d.getD 4 []) (iv183.d.getD 5 [])) = true := by
  decide +kernel

theorem iv183_ok : checkIv2 (lookDT treeK) admPre strsAll iv183 = true :=
  checkIv2_of_cases _ _ _ iv183 rfl rfl (by decide +kernel) iv183_c0 iv183_c1 iv183_c2 iv183_c3 iv183_c4

end ErdosComp
