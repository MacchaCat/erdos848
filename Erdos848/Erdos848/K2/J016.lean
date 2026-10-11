import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv16_c0 : below iv16.lo (caseIbQ (lookDT treeK) strsAll iv16.hi (iv16.p.getD 0 dPrm) (iv16.d.getD 0 [])) = true := by
  decide +kernel

theorem iv16_c1 : below iv16.lo (caseIIQ (lookDT treeK) admPre strsAll iv16.hi (iv16.p.getD 1 dPrm) (iv16.d.getD 1 [])) = true := by
  decide +kernel

theorem iv16_c2 : below iv16.lo (caseIII1Q (lookDT treeK) admPre strsAll iv16.hi (iv16.p.getD 2 dPrm) (iv16.d.getD 2 [])) = true := by
  decide +kernel

theorem iv16_c3 : below iv16.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv16.hi (iv16.p.getD 3 dPrm) (iv16.d.getD 3 [])) = true := by
  decide +kernel

theorem iv16_c4 : below iv16.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv16.hi (iv16.p.getD 4 dPrm) (iv16.d.getD 4 []) (iv16.d.getD 5 [])) = true := by
  decide +kernel

theorem iv16_ok : checkIv2 (lookDT treeK) admPre strsAll iv16 = true :=
  checkIv2_of_cases _ _ _ iv16 rfl rfl (by decide +kernel) iv16_c0 iv16_c1 iv16_c2 iv16_c3 iv16_c4

end ErdosComp
