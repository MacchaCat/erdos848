import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv331_c0 : below iv331.lo (caseIbQ (lookDT treeK) strsAll iv331.hi (iv331.p.getD 0 dPrm) (iv331.d.getD 0 [])) = true := by
  decide +kernel

theorem iv331_c1 : below iv331.lo (caseIIQ (lookDT treeK) admPre strsAll iv331.hi (iv331.p.getD 1 dPrm) (iv331.d.getD 1 [])) = true := by
  decide +kernel

theorem iv331_c2 : below iv331.lo (caseIII1Q (lookDT treeK) admPre strsAll iv331.hi (iv331.p.getD 2 dPrm) (iv331.d.getD 2 [])) = true := by
  decide +kernel

theorem iv331_c3 : below iv331.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv331.hi (iv331.p.getD 3 dPrm) (iv331.d.getD 3 [])) = true := by
  decide +kernel

theorem iv331_c4 : below iv331.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv331.hi (iv331.p.getD 4 dPrm) (iv331.d.getD 4 []) (iv331.d.getD 5 [])) = true := by
  decide +kernel

theorem iv331_ok : checkIv2 (lookDT treeK) admPre strsAll iv331 = true :=
  checkIv2_of_cases _ _ _ iv331 rfl rfl (by decide +kernel) iv331_c0 iv331_c1 iv331_c2 iv331_c3 iv331_c4

end ErdosComp
