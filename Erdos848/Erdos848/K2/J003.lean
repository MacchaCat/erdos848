import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv3_c0 : below iv3.lo (caseIbQ (lookDT treeK) strsAll iv3.hi (iv3.p.getD 0 dPrm) (iv3.d.getD 0 [])) = true := by
  decide +kernel

theorem iv3_c1 : below iv3.lo (caseIIQ (lookDT treeK) admPre strsAll iv3.hi (iv3.p.getD 1 dPrm) (iv3.d.getD 1 [])) = true := by
  decide +kernel

theorem iv3_c2 : below iv3.lo (caseIII1Q (lookDT treeK) admPre strsAll iv3.hi (iv3.p.getD 2 dPrm) (iv3.d.getD 2 [])) = true := by
  decide +kernel

theorem iv3_c3 : below iv3.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv3.hi (iv3.p.getD 3 dPrm) (iv3.d.getD 3 [])) = true := by
  decide +kernel

theorem iv3_c4 : below iv3.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv3.hi (iv3.p.getD 4 dPrm) (iv3.d.getD 4 []) (iv3.d.getD 5 [])) = true := by
  decide +kernel

theorem iv3_ok : checkIv2 (lookDT treeK) admPre strsAll iv3 = true :=
  checkIv2_of_cases _ _ _ iv3 rfl rfl (by decide +kernel) iv3_c0 iv3_c1 iv3_c2 iv3_c3 iv3_c4

end ErdosComp
