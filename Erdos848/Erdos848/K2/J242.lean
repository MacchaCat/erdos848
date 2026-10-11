import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv242_c0 : below iv242.lo (caseIbQ (lookDT treeK) strsAll iv242.hi (iv242.p.getD 0 dPrm) (iv242.d.getD 0 [])) = true := by
  decide +kernel

theorem iv242_c1 : below iv242.lo (caseIIQ (lookDT treeK) admPre strsAll iv242.hi (iv242.p.getD 1 dPrm) (iv242.d.getD 1 [])) = true := by
  decide +kernel

theorem iv242_c2 : below iv242.lo (caseIII1Q (lookDT treeK) admPre strsAll iv242.hi (iv242.p.getD 2 dPrm) (iv242.d.getD 2 [])) = true := by
  decide +kernel

theorem iv242_c3 : below iv242.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv242.hi (iv242.p.getD 3 dPrm) (iv242.d.getD 3 [])) = true := by
  decide +kernel

theorem iv242_c4 : below iv242.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv242.hi (iv242.p.getD 4 dPrm) (iv242.d.getD 4 []) (iv242.d.getD 5 [])) = true := by
  decide +kernel

theorem iv242_ok : checkIv2 (lookDT treeK) admPre strsAll iv242 = true :=
  checkIv2_of_cases _ _ _ iv242 rfl rfl (by decide +kernel) iv242_c0 iv242_c1 iv242_c2 iv242_c3 iv242_c4

end ErdosComp
