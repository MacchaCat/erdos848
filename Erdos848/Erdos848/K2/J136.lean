import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv136_c0 : below iv136.lo (caseIbQ (lookDT treeK) strsAll iv136.hi (iv136.p.getD 0 dPrm) (iv136.d.getD 0 [])) = true := by
  decide +kernel

theorem iv136_c1 : below iv136.lo (caseIIQ (lookDT treeK) admPre strsAll iv136.hi (iv136.p.getD 1 dPrm) (iv136.d.getD 1 [])) = true := by
  decide +kernel

theorem iv136_c2 : below iv136.lo (caseIII1Q (lookDT treeK) admPre strsAll iv136.hi (iv136.p.getD 2 dPrm) (iv136.d.getD 2 [])) = true := by
  decide +kernel

theorem iv136_c3 : below iv136.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv136.hi (iv136.p.getD 3 dPrm) (iv136.d.getD 3 [])) = true := by
  decide +kernel

theorem iv136_c4 : below iv136.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv136.hi (iv136.p.getD 4 dPrm) (iv136.d.getD 4 []) (iv136.d.getD 5 [])) = true := by
  decide +kernel

theorem iv136_ok : checkIv2 (lookDT treeK) admPre strsAll iv136 = true :=
  checkIv2_of_cases _ _ _ iv136 rfl rfl (by decide +kernel) iv136_c0 iv136_c1 iv136_c2 iv136_c3 iv136_c4

end ErdosComp
