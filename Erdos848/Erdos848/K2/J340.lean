import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv340_c0 : below iv340.lo (caseIbQ (lookDT treeK) strsAll iv340.hi (iv340.p.getD 0 dPrm) (iv340.d.getD 0 [])) = true := by
  decide +kernel

theorem iv340_c1 : below iv340.lo (caseIIQ (lookDT treeK) admPre strsAll iv340.hi (iv340.p.getD 1 dPrm) (iv340.d.getD 1 [])) = true := by
  decide +kernel

theorem iv340_c2 : below iv340.lo (caseIII1Q (lookDT treeK) admPre strsAll iv340.hi (iv340.p.getD 2 dPrm) (iv340.d.getD 2 [])) = true := by
  decide +kernel

theorem iv340_c3 : below iv340.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv340.hi (iv340.p.getD 3 dPrm) (iv340.d.getD 3 [])) = true := by
  decide +kernel

theorem iv340_c4 : below iv340.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv340.hi (iv340.p.getD 4 dPrm) (iv340.d.getD 4 []) (iv340.d.getD 5 [])) = true := by
  decide +kernel

theorem iv340_ok : checkIv2 (lookDT treeK) admPre strsAll iv340 = true :=
  checkIv2_of_cases _ _ _ iv340 rfl rfl (by decide +kernel) iv340_c0 iv340_c1 iv340_c2 iv340_c3 iv340_c4

end ErdosComp
