import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv221_c0 : below iv221.lo (caseIbQ (lookDT treeK) strsAll iv221.hi (iv221.p.getD 0 dPrm) (iv221.d.getD 0 [])) = true := by
  decide +kernel

theorem iv221_c1 : below iv221.lo (caseIIQ (lookDT treeK) admPre strsAll iv221.hi (iv221.p.getD 1 dPrm) (iv221.d.getD 1 [])) = true := by
  decide +kernel

theorem iv221_c2 : below iv221.lo (caseIII1Q (lookDT treeK) admPre strsAll iv221.hi (iv221.p.getD 2 dPrm) (iv221.d.getD 2 [])) = true := by
  decide +kernel

theorem iv221_c3 : below iv221.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv221.hi (iv221.p.getD 3 dPrm) (iv221.d.getD 3 [])) = true := by
  decide +kernel

theorem iv221_c4 : below iv221.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv221.hi (iv221.p.getD 4 dPrm) (iv221.d.getD 4 []) (iv221.d.getD 5 [])) = true := by
  decide +kernel

theorem iv221_ok : checkIv2 (lookDT treeK) admPre strsAll iv221 = true :=
  checkIv2_of_cases _ _ _ iv221 rfl rfl (by decide +kernel) iv221_c0 iv221_c1 iv221_c2 iv221_c3 iv221_c4

end ErdosComp
