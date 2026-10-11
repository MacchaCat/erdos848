import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv180_c0 : below iv180.lo (caseIbQ (lookDT treeK) strsAll iv180.hi (iv180.p.getD 0 dPrm) (iv180.d.getD 0 [])) = true := by
  decide +kernel

theorem iv180_c1 : below iv180.lo (caseIIQ (lookDT treeK) admPre strsAll iv180.hi (iv180.p.getD 1 dPrm) (iv180.d.getD 1 [])) = true := by
  decide +kernel

theorem iv180_c2 : below iv180.lo (caseIII1Q (lookDT treeK) admPre strsAll iv180.hi (iv180.p.getD 2 dPrm) (iv180.d.getD 2 [])) = true := by
  decide +kernel

theorem iv180_c3 : below iv180.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv180.hi (iv180.p.getD 3 dPrm) (iv180.d.getD 3 [])) = true := by
  decide +kernel

theorem iv180_c4 : below iv180.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv180.hi (iv180.p.getD 4 dPrm) (iv180.d.getD 4 []) (iv180.d.getD 5 [])) = true := by
  decide +kernel

theorem iv180_ok : checkIv2 (lookDT treeK) admPre strsAll iv180 = true :=
  checkIv2_of_cases _ _ _ iv180 rfl rfl (by decide +kernel) iv180_c0 iv180_c1 iv180_c2 iv180_c3 iv180_c4

end ErdosComp
