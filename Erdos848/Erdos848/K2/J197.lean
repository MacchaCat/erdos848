import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv197_c0 : below iv197.lo (caseIbQ (lookDT treeK) strsAll iv197.hi (iv197.p.getD 0 dPrm) (iv197.d.getD 0 [])) = true := by
  decide +kernel

theorem iv197_c1 : below iv197.lo (caseIIQ (lookDT treeK) admPre strsAll iv197.hi (iv197.p.getD 1 dPrm) (iv197.d.getD 1 [])) = true := by
  decide +kernel

theorem iv197_c2 : below iv197.lo (caseIII1Q (lookDT treeK) admPre strsAll iv197.hi (iv197.p.getD 2 dPrm) (iv197.d.getD 2 [])) = true := by
  decide +kernel

theorem iv197_c3 : below iv197.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv197.hi (iv197.p.getD 3 dPrm) (iv197.d.getD 3 [])) = true := by
  decide +kernel

theorem iv197_c4 : below iv197.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv197.hi (iv197.p.getD 4 dPrm) (iv197.d.getD 4 []) (iv197.d.getD 5 [])) = true := by
  decide +kernel

theorem iv197_ok : checkIv2 (lookDT treeK) admPre strsAll iv197 = true :=
  checkIv2_of_cases _ _ _ iv197 rfl rfl (by decide +kernel) iv197_c0 iv197_c1 iv197_c2 iv197_c3 iv197_c4

end ErdosComp
