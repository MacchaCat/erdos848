import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv165_c0 : below iv165.lo (caseIbQ (lookDT treeK) strsAll iv165.hi (iv165.p.getD 0 dPrm) (iv165.d.getD 0 [])) = true := by
  decide +kernel

theorem iv165_c1 : below iv165.lo (caseIIQ (lookDT treeK) admPre strsAll iv165.hi (iv165.p.getD 1 dPrm) (iv165.d.getD 1 [])) = true := by
  decide +kernel

theorem iv165_c2 : below iv165.lo (caseIII1Q (lookDT treeK) admPre strsAll iv165.hi (iv165.p.getD 2 dPrm) (iv165.d.getD 2 [])) = true := by
  decide +kernel

theorem iv165_c3 : below iv165.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv165.hi (iv165.p.getD 3 dPrm) (iv165.d.getD 3 [])) = true := by
  decide +kernel

theorem iv165_c4 : below iv165.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv165.hi (iv165.p.getD 4 dPrm) (iv165.d.getD 4 []) (iv165.d.getD 5 [])) = true := by
  decide +kernel

theorem iv165_ok : checkIv2 (lookDT treeK) admPre strsAll iv165 = true :=
  checkIv2_of_cases _ _ _ iv165 rfl rfl (by decide +kernel) iv165_c0 iv165_c1 iv165_c2 iv165_c3 iv165_c4

end ErdosComp
