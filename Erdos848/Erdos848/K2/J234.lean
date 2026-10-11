import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv234_c0 : below iv234.lo (caseIbQ (lookDT treeK) strsAll iv234.hi (iv234.p.getD 0 dPrm) (iv234.d.getD 0 [])) = true := by
  decide +kernel

theorem iv234_c1 : below iv234.lo (caseIIQ (lookDT treeK) admPre strsAll iv234.hi (iv234.p.getD 1 dPrm) (iv234.d.getD 1 [])) = true := by
  decide +kernel

theorem iv234_c2 : below iv234.lo (caseIII1Q (lookDT treeK) admPre strsAll iv234.hi (iv234.p.getD 2 dPrm) (iv234.d.getD 2 [])) = true := by
  decide +kernel

theorem iv234_c3 : below iv234.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv234.hi (iv234.p.getD 3 dPrm) (iv234.d.getD 3 [])) = true := by
  decide +kernel

theorem iv234_c4 : below iv234.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv234.hi (iv234.p.getD 4 dPrm) (iv234.d.getD 4 []) (iv234.d.getD 5 [])) = true := by
  decide +kernel

theorem iv234_ok : checkIv2 (lookDT treeK) admPre strsAll iv234 = true :=
  checkIv2_of_cases _ _ _ iv234 rfl rfl (by decide +kernel) iv234_c0 iv234_c1 iv234_c2 iv234_c3 iv234_c4

end ErdosComp
