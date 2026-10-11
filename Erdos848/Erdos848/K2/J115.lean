import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv115_c0 : below iv115.lo (caseIbQ (lookDT treeK) strsAll iv115.hi (iv115.p.getD 0 dPrm) (iv115.d.getD 0 [])) = true := by
  decide +kernel

theorem iv115_c1 : below iv115.lo (caseIIQ (lookDT treeK) admPre strsAll iv115.hi (iv115.p.getD 1 dPrm) (iv115.d.getD 1 [])) = true := by
  decide +kernel

theorem iv115_c2 : below iv115.lo (caseIII1Q (lookDT treeK) admPre strsAll iv115.hi (iv115.p.getD 2 dPrm) (iv115.d.getD 2 [])) = true := by
  decide +kernel

theorem iv115_c3 : below iv115.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv115.hi (iv115.p.getD 3 dPrm) (iv115.d.getD 3 [])) = true := by
  decide +kernel

theorem iv115_c4 : below iv115.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv115.hi (iv115.p.getD 4 dPrm) (iv115.d.getD 4 []) (iv115.d.getD 5 [])) = true := by
  decide +kernel

theorem iv115_ok : checkIv2 (lookDT treeK) admPre strsAll iv115 = true :=
  checkIv2_of_cases _ _ _ iv115 rfl rfl (by decide +kernel) iv115_c0 iv115_c1 iv115_c2 iv115_c3 iv115_c4

end ErdosComp
