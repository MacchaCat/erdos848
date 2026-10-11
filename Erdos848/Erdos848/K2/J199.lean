import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv199_c0 : below iv199.lo (caseIbQ (lookDT treeK) strsAll iv199.hi (iv199.p.getD 0 dPrm) (iv199.d.getD 0 [])) = true := by
  decide +kernel

theorem iv199_c1 : below iv199.lo (caseIIQ (lookDT treeK) admPre strsAll iv199.hi (iv199.p.getD 1 dPrm) (iv199.d.getD 1 [])) = true := by
  decide +kernel

theorem iv199_c2 : below iv199.lo (caseIII1Q (lookDT treeK) admPre strsAll iv199.hi (iv199.p.getD 2 dPrm) (iv199.d.getD 2 [])) = true := by
  decide +kernel

theorem iv199_c3 : below iv199.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv199.hi (iv199.p.getD 3 dPrm) (iv199.d.getD 3 [])) = true := by
  decide +kernel

theorem iv199_c4 : below iv199.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv199.hi (iv199.p.getD 4 dPrm) (iv199.d.getD 4 []) (iv199.d.getD 5 [])) = true := by
  decide +kernel

theorem iv199_ok : checkIv2 (lookDT treeK) admPre strsAll iv199 = true :=
  checkIv2_of_cases _ _ _ iv199 rfl rfl (by decide +kernel) iv199_c0 iv199_c1 iv199_c2 iv199_c3 iv199_c4

end ErdosComp
