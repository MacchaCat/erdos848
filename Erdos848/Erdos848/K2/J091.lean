import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv91_c0 : below iv91.lo (caseIbQ (lookDT treeK) strsAll iv91.hi (iv91.p.getD 0 dPrm) (iv91.d.getD 0 [])) = true := by
  decide +kernel

theorem iv91_c1 : below iv91.lo (caseIIQ (lookDT treeK) admPre strsAll iv91.hi (iv91.p.getD 1 dPrm) (iv91.d.getD 1 [])) = true := by
  decide +kernel

theorem iv91_c2 : below iv91.lo (caseIII1Q (lookDT treeK) admPre strsAll iv91.hi (iv91.p.getD 2 dPrm) (iv91.d.getD 2 [])) = true := by
  decide +kernel

theorem iv91_c3 : below iv91.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv91.hi (iv91.p.getD 3 dPrm) (iv91.d.getD 3 [])) = true := by
  decide +kernel

theorem iv91_c4 : below iv91.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv91.hi (iv91.p.getD 4 dPrm) (iv91.d.getD 4 []) (iv91.d.getD 5 [])) = true := by
  decide +kernel

theorem iv91_ok : checkIv2 (lookDT treeK) admPre strsAll iv91 = true :=
  checkIv2_of_cases _ _ _ iv91 rfl rfl (by decide +kernel) iv91_c0 iv91_c1 iv91_c2 iv91_c3 iv91_c4

end ErdosComp
