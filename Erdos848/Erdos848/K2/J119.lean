import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv119_c0 : below iv119.lo (caseIbQ (lookDT treeK) strsAll iv119.hi (iv119.p.getD 0 dPrm) (iv119.d.getD 0 [])) = true := by
  decide +kernel

theorem iv119_c1 : below iv119.lo (caseIIQ (lookDT treeK) admPre strsAll iv119.hi (iv119.p.getD 1 dPrm) (iv119.d.getD 1 [])) = true := by
  decide +kernel

theorem iv119_c2 : below iv119.lo (caseIII1Q (lookDT treeK) admPre strsAll iv119.hi (iv119.p.getD 2 dPrm) (iv119.d.getD 2 [])) = true := by
  decide +kernel

theorem iv119_c3 : below iv119.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv119.hi (iv119.p.getD 3 dPrm) (iv119.d.getD 3 [])) = true := by
  decide +kernel

theorem iv119_c4 : below iv119.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv119.hi (iv119.p.getD 4 dPrm) (iv119.d.getD 4 []) (iv119.d.getD 5 [])) = true := by
  decide +kernel

theorem iv119_ok : checkIv2 (lookDT treeK) admPre strsAll iv119 = true :=
  checkIv2_of_cases _ _ _ iv119 rfl rfl (by decide +kernel) iv119_c0 iv119_c1 iv119_c2 iv119_c3 iv119_c4

end ErdosComp
