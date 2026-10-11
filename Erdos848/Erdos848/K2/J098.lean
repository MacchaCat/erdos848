import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv98_c0 : below iv98.lo (caseIbQ (lookDT treeK) strsAll iv98.hi (iv98.p.getD 0 dPrm) (iv98.d.getD 0 [])) = true := by
  decide +kernel

theorem iv98_c1 : below iv98.lo (caseIIQ (lookDT treeK) admPre strsAll iv98.hi (iv98.p.getD 1 dPrm) (iv98.d.getD 1 [])) = true := by
  decide +kernel

theorem iv98_c2 : below iv98.lo (caseIII1Q (lookDT treeK) admPre strsAll iv98.hi (iv98.p.getD 2 dPrm) (iv98.d.getD 2 [])) = true := by
  decide +kernel

theorem iv98_c3 : below iv98.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv98.hi (iv98.p.getD 3 dPrm) (iv98.d.getD 3 [])) = true := by
  decide +kernel

theorem iv98_c4 : below iv98.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv98.hi (iv98.p.getD 4 dPrm) (iv98.d.getD 4 []) (iv98.d.getD 5 [])) = true := by
  decide +kernel

theorem iv98_ok : checkIv2 (lookDT treeK) admPre strsAll iv98 = true :=
  checkIv2_of_cases _ _ _ iv98 rfl rfl (by decide +kernel) iv98_c0 iv98_c1 iv98_c2 iv98_c3 iv98_c4

end ErdosComp
