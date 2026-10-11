import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv23_c0 : below iv23.lo (caseIbQ (lookDT treeK) strsAll iv23.hi (iv23.p.getD 0 dPrm) (iv23.d.getD 0 [])) = true := by
  decide +kernel

theorem iv23_c1 : below iv23.lo (caseIIQ (lookDT treeK) admPre strsAll iv23.hi (iv23.p.getD 1 dPrm) (iv23.d.getD 1 [])) = true := by
  decide +kernel

theorem iv23_c2 : below iv23.lo (caseIII1Q (lookDT treeK) admPre strsAll iv23.hi (iv23.p.getD 2 dPrm) (iv23.d.getD 2 [])) = true := by
  decide +kernel

theorem iv23_c3 : below iv23.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv23.hi (iv23.p.getD 3 dPrm) (iv23.d.getD 3 [])) = true := by
  decide +kernel

theorem iv23_c4 : below iv23.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv23.hi (iv23.p.getD 4 dPrm) (iv23.d.getD 4 []) (iv23.d.getD 5 [])) = true := by
  decide +kernel

theorem iv23_ok : checkIv2 (lookDT treeK) admPre strsAll iv23 = true :=
  checkIv2_of_cases _ _ _ iv23 rfl rfl (by decide +kernel) iv23_c0 iv23_c1 iv23_c2 iv23_c3 iv23_c4

end ErdosComp
