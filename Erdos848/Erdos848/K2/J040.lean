import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv40_c0 : below iv40.lo (caseIbQ (lookDT treeK) strsAll iv40.hi (iv40.p.getD 0 dPrm) (iv40.d.getD 0 [])) = true := by
  decide +kernel

theorem iv40_c1 : below iv40.lo (caseIIQ (lookDT treeK) admPre strsAll iv40.hi (iv40.p.getD 1 dPrm) (iv40.d.getD 1 [])) = true := by
  decide +kernel

theorem iv40_c2 : below iv40.lo (caseIII1Q (lookDT treeK) admPre strsAll iv40.hi (iv40.p.getD 2 dPrm) (iv40.d.getD 2 [])) = true := by
  decide +kernel

theorem iv40_c3 : below iv40.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv40.hi (iv40.p.getD 3 dPrm) (iv40.d.getD 3 [])) = true := by
  decide +kernel

theorem iv40_c4 : below iv40.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv40.hi (iv40.p.getD 4 dPrm) (iv40.d.getD 4 []) (iv40.d.getD 5 [])) = true := by
  decide +kernel

theorem iv40_ok : checkIv2 (lookDT treeK) admPre strsAll iv40 = true :=
  checkIv2_of_cases _ _ _ iv40 rfl rfl (by decide +kernel) iv40_c0 iv40_c1 iv40_c2 iv40_c3 iv40_c4

end ErdosComp
