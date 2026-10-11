import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv261_c0 : below iv261.lo (caseIbQ (lookDT treeK) strsAll iv261.hi (iv261.p.getD 0 dPrm) (iv261.d.getD 0 [])) = true := by
  decide +kernel

theorem iv261_c1 : below iv261.lo (caseIIQ (lookDT treeK) admPre strsAll iv261.hi (iv261.p.getD 1 dPrm) (iv261.d.getD 1 [])) = true := by
  decide +kernel

theorem iv261_c2 : below iv261.lo (caseIII1Q (lookDT treeK) admPre strsAll iv261.hi (iv261.p.getD 2 dPrm) (iv261.d.getD 2 [])) = true := by
  decide +kernel

theorem iv261_c3 : below iv261.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv261.hi (iv261.p.getD 3 dPrm) (iv261.d.getD 3 [])) = true := by
  decide +kernel

theorem iv261_c4 : below iv261.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv261.hi (iv261.p.getD 4 dPrm) (iv261.d.getD 4 []) (iv261.d.getD 5 [])) = true := by
  decide +kernel

theorem iv261_ok : checkIv2 (lookDT treeK) admPre strsAll iv261 = true :=
  checkIv2_of_cases _ _ _ iv261 rfl rfl (by decide +kernel) iv261_c0 iv261_c1 iv261_c2 iv261_c3 iv261_c4

end ErdosComp
