import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv244_c0 : below iv244.lo (caseIbQ (lookDT treeK) strsAll iv244.hi (iv244.p.getD 0 dPrm) (iv244.d.getD 0 [])) = true := by
  decide +kernel

theorem iv244_c1 : below iv244.lo (caseIIQ (lookDT treeK) admPre strsAll iv244.hi (iv244.p.getD 1 dPrm) (iv244.d.getD 1 [])) = true := by
  decide +kernel

theorem iv244_c2 : below iv244.lo (caseIII1Q (lookDT treeK) admPre strsAll iv244.hi (iv244.p.getD 2 dPrm) (iv244.d.getD 2 [])) = true := by
  decide +kernel

theorem iv244_c3 : below iv244.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv244.hi (iv244.p.getD 3 dPrm) (iv244.d.getD 3 [])) = true := by
  decide +kernel

theorem iv244_c4 : below iv244.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv244.hi (iv244.p.getD 4 dPrm) (iv244.d.getD 4 []) (iv244.d.getD 5 [])) = true := by
  decide +kernel

theorem iv244_ok : checkIv2 (lookDT treeK) admPre strsAll iv244 = true :=
  checkIv2_of_cases _ _ _ iv244 rfl rfl (by decide +kernel) iv244_c0 iv244_c1 iv244_c2 iv244_c3 iv244_c4

end ErdosComp
