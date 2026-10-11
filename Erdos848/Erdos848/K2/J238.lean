import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv238_c0 : below iv238.lo (caseIbQ (lookDT treeK) strsAll iv238.hi (iv238.p.getD 0 dPrm) (iv238.d.getD 0 [])) = true := by
  decide +kernel

theorem iv238_c1 : below iv238.lo (caseIIQ (lookDT treeK) admPre strsAll iv238.hi (iv238.p.getD 1 dPrm) (iv238.d.getD 1 [])) = true := by
  decide +kernel

theorem iv238_c2 : below iv238.lo (caseIII1Q (lookDT treeK) admPre strsAll iv238.hi (iv238.p.getD 2 dPrm) (iv238.d.getD 2 [])) = true := by
  decide +kernel

theorem iv238_c3 : below iv238.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv238.hi (iv238.p.getD 3 dPrm) (iv238.d.getD 3 [])) = true := by
  decide +kernel

theorem iv238_c4 : below iv238.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv238.hi (iv238.p.getD 4 dPrm) (iv238.d.getD 4 []) (iv238.d.getD 5 [])) = true := by
  decide +kernel

theorem iv238_ok : checkIv2 (lookDT treeK) admPre strsAll iv238 = true :=
  checkIv2_of_cases _ _ _ iv238 rfl rfl (by decide +kernel) iv238_c0 iv238_c1 iv238_c2 iv238_c3 iv238_c4

end ErdosComp
