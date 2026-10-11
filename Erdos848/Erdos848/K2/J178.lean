import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv178_c0 : below iv178.lo (caseIbQ (lookDT treeK) strsAll iv178.hi (iv178.p.getD 0 dPrm) (iv178.d.getD 0 [])) = true := by
  decide +kernel

theorem iv178_c1 : below iv178.lo (caseIIQ (lookDT treeK) admPre strsAll iv178.hi (iv178.p.getD 1 dPrm) (iv178.d.getD 1 [])) = true := by
  decide +kernel

theorem iv178_c2 : below iv178.lo (caseIII1Q (lookDT treeK) admPre strsAll iv178.hi (iv178.p.getD 2 dPrm) (iv178.d.getD 2 [])) = true := by
  decide +kernel

theorem iv178_c3 : below iv178.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv178.hi (iv178.p.getD 3 dPrm) (iv178.d.getD 3 [])) = true := by
  decide +kernel

theorem iv178_c4 : below iv178.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv178.hi (iv178.p.getD 4 dPrm) (iv178.d.getD 4 []) (iv178.d.getD 5 [])) = true := by
  decide +kernel

theorem iv178_ok : checkIv2 (lookDT treeK) admPre strsAll iv178 = true :=
  checkIv2_of_cases _ _ _ iv178 rfl rfl (by decide +kernel) iv178_c0 iv178_c1 iv178_c2 iv178_c3 iv178_c4

end ErdosComp
