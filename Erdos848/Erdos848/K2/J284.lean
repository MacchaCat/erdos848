import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv284_c0 : below iv284.lo (caseIbQ (lookDT treeK) strsAll iv284.hi (iv284.p.getD 0 dPrm) (iv284.d.getD 0 [])) = true := by
  decide +kernel

theorem iv284_c1 : below iv284.lo (caseIIQ (lookDT treeK) admPre strsAll iv284.hi (iv284.p.getD 1 dPrm) (iv284.d.getD 1 [])) = true := by
  decide +kernel

theorem iv284_c2 : below iv284.lo (caseIII1Q (lookDT treeK) admPre strsAll iv284.hi (iv284.p.getD 2 dPrm) (iv284.d.getD 2 [])) = true := by
  decide +kernel

theorem iv284_c3 : below iv284.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv284.hi (iv284.p.getD 3 dPrm) (iv284.d.getD 3 [])) = true := by
  decide +kernel

theorem iv284_c4 : below iv284.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv284.hi (iv284.p.getD 4 dPrm) (iv284.d.getD 4 []) (iv284.d.getD 5 [])) = true := by
  decide +kernel

theorem iv284_ok : checkIv2 (lookDT treeK) admPre strsAll iv284 = true :=
  checkIv2_of_cases _ _ _ iv284 rfl rfl (by decide +kernel) iv284_c0 iv284_c1 iv284_c2 iv284_c3 iv284_c4

end ErdosComp
