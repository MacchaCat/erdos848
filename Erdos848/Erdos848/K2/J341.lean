import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv341_c0 : below iv341.lo (caseIbQ (lookDT treeK) strsAll iv341.hi (iv341.p.getD 0 dPrm) (iv341.d.getD 0 [])) = true := by
  decide +kernel

theorem iv341_c1 : below iv341.lo (caseIIQ (lookDT treeK) admPre strsAll iv341.hi (iv341.p.getD 1 dPrm) (iv341.d.getD 1 [])) = true := by
  decide +kernel

theorem iv341_c2 : below iv341.lo (caseIII1Q (lookDT treeK) admPre strsAll iv341.hi (iv341.p.getD 2 dPrm) (iv341.d.getD 2 [])) = true := by
  decide +kernel

theorem iv341_c3 : below iv341.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv341.hi (iv341.p.getD 3 dPrm) (iv341.d.getD 3 [])) = true := by
  decide +kernel

theorem iv341_c4 : below iv341.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv341.hi (iv341.p.getD 4 dPrm) (iv341.d.getD 4 []) (iv341.d.getD 5 [])) = true := by
  decide +kernel

theorem iv341_ok : checkIv2 (lookDT treeK) admPre strsAll iv341 = true :=
  checkIv2_of_cases _ _ _ iv341 rfl rfl (by decide +kernel) iv341_c0 iv341_c1 iv341_c2 iv341_c3 iv341_c4

end ErdosComp
