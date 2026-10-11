import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv213_c0 : below iv213.lo (caseIbQ (lookDT treeK) strsAll iv213.hi (iv213.p.getD 0 dPrm) (iv213.d.getD 0 [])) = true := by
  decide +kernel

theorem iv213_c1 : below iv213.lo (caseIIQ (lookDT treeK) admPre strsAll iv213.hi (iv213.p.getD 1 dPrm) (iv213.d.getD 1 [])) = true := by
  decide +kernel

theorem iv213_c2 : below iv213.lo (caseIII1Q (lookDT treeK) admPre strsAll iv213.hi (iv213.p.getD 2 dPrm) (iv213.d.getD 2 [])) = true := by
  decide +kernel

theorem iv213_c3 : below iv213.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv213.hi (iv213.p.getD 3 dPrm) (iv213.d.getD 3 [])) = true := by
  decide +kernel

theorem iv213_c4 : below iv213.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv213.hi (iv213.p.getD 4 dPrm) (iv213.d.getD 4 []) (iv213.d.getD 5 [])) = true := by
  decide +kernel

theorem iv213_ok : checkIv2 (lookDT treeK) admPre strsAll iv213 = true :=
  checkIv2_of_cases _ _ _ iv213 rfl rfl (by decide +kernel) iv213_c0 iv213_c1 iv213_c2 iv213_c3 iv213_c4

end ErdosComp
