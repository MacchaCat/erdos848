import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv253_c0 : below iv253.lo (caseIbQ (lookDT treeK) strsAll iv253.hi (iv253.p.getD 0 dPrm) (iv253.d.getD 0 [])) = true := by
  decide +kernel

theorem iv253_c1 : below iv253.lo (caseIIQ (lookDT treeK) admPre strsAll iv253.hi (iv253.p.getD 1 dPrm) (iv253.d.getD 1 [])) = true := by
  decide +kernel

theorem iv253_c2 : below iv253.lo (caseIII1Q (lookDT treeK) admPre strsAll iv253.hi (iv253.p.getD 2 dPrm) (iv253.d.getD 2 [])) = true := by
  decide +kernel

theorem iv253_c3 : below iv253.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv253.hi (iv253.p.getD 3 dPrm) (iv253.d.getD 3 [])) = true := by
  decide +kernel

theorem iv253_c4 : below iv253.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv253.hi (iv253.p.getD 4 dPrm) (iv253.d.getD 4 []) (iv253.d.getD 5 [])) = true := by
  decide +kernel

theorem iv253_ok : checkIv2 (lookDT treeK) admPre strsAll iv253 = true :=
  checkIv2_of_cases _ _ _ iv253 rfl rfl (by decide +kernel) iv253_c0 iv253_c1 iv253_c2 iv253_c3 iv253_c4

end ErdosComp
