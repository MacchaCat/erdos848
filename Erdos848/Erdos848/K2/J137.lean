import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv137_c0 : below iv137.lo (caseIbQ (lookDT treeK) strsAll iv137.hi (iv137.p.getD 0 dPrm) (iv137.d.getD 0 [])) = true := by
  decide +kernel

theorem iv137_c1 : below iv137.lo (caseIIQ (lookDT treeK) admPre strsAll iv137.hi (iv137.p.getD 1 dPrm) (iv137.d.getD 1 [])) = true := by
  decide +kernel

theorem iv137_c2 : below iv137.lo (caseIII1Q (lookDT treeK) admPre strsAll iv137.hi (iv137.p.getD 2 dPrm) (iv137.d.getD 2 [])) = true := by
  decide +kernel

theorem iv137_c3 : below iv137.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv137.hi (iv137.p.getD 3 dPrm) (iv137.d.getD 3 [])) = true := by
  decide +kernel

theorem iv137_c4 : below iv137.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv137.hi (iv137.p.getD 4 dPrm) (iv137.d.getD 4 []) (iv137.d.getD 5 [])) = true := by
  decide +kernel

theorem iv137_ok : checkIv2 (lookDT treeK) admPre strsAll iv137 = true :=
  checkIv2_of_cases _ _ _ iv137 rfl rfl (by decide +kernel) iv137_c0 iv137_c1 iv137_c2 iv137_c3 iv137_c4

end ErdosComp
