import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv273_c0 : below iv273.lo (caseIbQ (lookDT treeK) strsAll iv273.hi (iv273.p.getD 0 dPrm) (iv273.d.getD 0 [])) = true := by
  decide +kernel

theorem iv273_c1 : below iv273.lo (caseIIQ (lookDT treeK) admPre strsAll iv273.hi (iv273.p.getD 1 dPrm) (iv273.d.getD 1 [])) = true := by
  decide +kernel

theorem iv273_c2 : below iv273.lo (caseIII1Q (lookDT treeK) admPre strsAll iv273.hi (iv273.p.getD 2 dPrm) (iv273.d.getD 2 [])) = true := by
  decide +kernel

theorem iv273_c3 : below iv273.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv273.hi (iv273.p.getD 3 dPrm) (iv273.d.getD 3 [])) = true := by
  decide +kernel

theorem iv273_c4 : below iv273.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv273.hi (iv273.p.getD 4 dPrm) (iv273.d.getD 4 []) (iv273.d.getD 5 [])) = true := by
  decide +kernel

theorem iv273_ok : checkIv2 (lookDT treeK) admPre strsAll iv273 = true :=
  checkIv2_of_cases _ _ _ iv273 rfl rfl (by decide +kernel) iv273_c0 iv273_c1 iv273_c2 iv273_c3 iv273_c4

end ErdosComp
