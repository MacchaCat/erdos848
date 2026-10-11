import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv161_c0 : below iv161.lo (caseIbQ (lookDT treeK) strsAll iv161.hi (iv161.p.getD 0 dPrm) (iv161.d.getD 0 [])) = true := by
  decide +kernel

theorem iv161_c1 : below iv161.lo (caseIIQ (lookDT treeK) admPre strsAll iv161.hi (iv161.p.getD 1 dPrm) (iv161.d.getD 1 [])) = true := by
  decide +kernel

theorem iv161_c2 : below iv161.lo (caseIII1Q (lookDT treeK) admPre strsAll iv161.hi (iv161.p.getD 2 dPrm) (iv161.d.getD 2 [])) = true := by
  decide +kernel

theorem iv161_c3 : below iv161.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv161.hi (iv161.p.getD 3 dPrm) (iv161.d.getD 3 [])) = true := by
  decide +kernel

theorem iv161_c4 : below iv161.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv161.hi (iv161.p.getD 4 dPrm) (iv161.d.getD 4 []) (iv161.d.getD 5 [])) = true := by
  decide +kernel

theorem iv161_ok : checkIv2 (lookDT treeK) admPre strsAll iv161 = true :=
  checkIv2_of_cases _ _ _ iv161 rfl rfl (by decide +kernel) iv161_c0 iv161_c1 iv161_c2 iv161_c3 iv161_c4

end ErdosComp
