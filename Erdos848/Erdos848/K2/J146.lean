import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv146_c0 : below iv146.lo (caseIbQ (lookDT treeK) strsAll iv146.hi (iv146.p.getD 0 dPrm) (iv146.d.getD 0 [])) = true := by
  decide +kernel

theorem iv146_c1 : below iv146.lo (caseIIQ (lookDT treeK) admPre strsAll iv146.hi (iv146.p.getD 1 dPrm) (iv146.d.getD 1 [])) = true := by
  decide +kernel

theorem iv146_c2 : below iv146.lo (caseIII1Q (lookDT treeK) admPre strsAll iv146.hi (iv146.p.getD 2 dPrm) (iv146.d.getD 2 [])) = true := by
  decide +kernel

theorem iv146_c3 : below iv146.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv146.hi (iv146.p.getD 3 dPrm) (iv146.d.getD 3 [])) = true := by
  decide +kernel

theorem iv146_c4 : below iv146.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv146.hi (iv146.p.getD 4 dPrm) (iv146.d.getD 4 []) (iv146.d.getD 5 [])) = true := by
  decide +kernel

theorem iv146_ok : checkIv2 (lookDT treeK) admPre strsAll iv146 = true :=
  checkIv2_of_cases _ _ _ iv146 rfl rfl (by decide +kernel) iv146_c0 iv146_c1 iv146_c2 iv146_c3 iv146_c4

end ErdosComp
