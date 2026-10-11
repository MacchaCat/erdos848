import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv2_c0 : below iv2.lo (caseIbQ (lookDT treeK) strsAll iv2.hi (iv2.p.getD 0 dPrm) (iv2.d.getD 0 [])) = true := by
  decide +kernel

theorem iv2_c1 : below iv2.lo (caseIIQ (lookDT treeK) admPre strsAll iv2.hi (iv2.p.getD 1 dPrm) (iv2.d.getD 1 [])) = true := by
  decide +kernel

theorem iv2_c2 : below iv2.lo (caseIII1Q (lookDT treeK) admPre strsAll iv2.hi (iv2.p.getD 2 dPrm) (iv2.d.getD 2 [])) = true := by
  decide +kernel

theorem iv2_c3 : below iv2.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv2.hi (iv2.p.getD 3 dPrm) (iv2.d.getD 3 [])) = true := by
  decide +kernel

theorem iv2_c4 : below iv2.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv2.hi (iv2.p.getD 4 dPrm) (iv2.d.getD 4 []) (iv2.d.getD 5 [])) = true := by
  decide +kernel

theorem iv2_ok : checkIv2 (lookDT treeK) admPre strsAll iv2 = true :=
  checkIv2_of_cases _ _ _ iv2 rfl rfl (by decide +kernel) iv2_c0 iv2_c1 iv2_c2 iv2_c3 iv2_c4

end ErdosComp
