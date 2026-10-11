import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv293_c0 : below iv293.lo (caseIbQ (lookDT treeK) strsAll iv293.hi (iv293.p.getD 0 dPrm) (iv293.d.getD 0 [])) = true := by
  decide +kernel

theorem iv293_c1 : below iv293.lo (caseIIQ (lookDT treeK) admPre strsAll iv293.hi (iv293.p.getD 1 dPrm) (iv293.d.getD 1 [])) = true := by
  decide +kernel

theorem iv293_c2 : below iv293.lo (caseIII1Q (lookDT treeK) admPre strsAll iv293.hi (iv293.p.getD 2 dPrm) (iv293.d.getD 2 [])) = true := by
  decide +kernel

theorem iv293_c3 : below iv293.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv293.hi (iv293.p.getD 3 dPrm) (iv293.d.getD 3 [])) = true := by
  decide +kernel

theorem iv293_c4 : below iv293.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv293.hi (iv293.p.getD 4 dPrm) (iv293.d.getD 4 []) (iv293.d.getD 5 [])) = true := by
  decide +kernel

theorem iv293_ok : checkIv2 (lookDT treeK) admPre strsAll iv293 = true :=
  checkIv2_of_cases _ _ _ iv293 rfl rfl (by decide +kernel) iv293_c0 iv293_c1 iv293_c2 iv293_c3 iv293_c4

end ErdosComp
