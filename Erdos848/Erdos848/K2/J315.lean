import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv315_c0 : below iv315.lo (caseIbQ (lookDT treeK) strsAll iv315.hi (iv315.p.getD 0 dPrm) (iv315.d.getD 0 [])) = true := by
  decide +kernel

theorem iv315_c1 : below iv315.lo (caseIIQ (lookDT treeK) admPre strsAll iv315.hi (iv315.p.getD 1 dPrm) (iv315.d.getD 1 [])) = true := by
  decide +kernel

theorem iv315_c2 : below iv315.lo (caseIII1Q (lookDT treeK) admPre strsAll iv315.hi (iv315.p.getD 2 dPrm) (iv315.d.getD 2 [])) = true := by
  decide +kernel

theorem iv315_c3 : below iv315.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv315.hi (iv315.p.getD 3 dPrm) (iv315.d.getD 3 [])) = true := by
  decide +kernel

theorem iv315_c4 : below iv315.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv315.hi (iv315.p.getD 4 dPrm) (iv315.d.getD 4 []) (iv315.d.getD 5 [])) = true := by
  decide +kernel

theorem iv315_ok : checkIv2 (lookDT treeK) admPre strsAll iv315 = true :=
  checkIv2_of_cases _ _ _ iv315 rfl rfl (by decide +kernel) iv315_c0 iv315_c1 iv315_c2 iv315_c3 iv315_c4

end ErdosComp
