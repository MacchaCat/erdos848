import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv51_c0 : below iv51.lo (caseIbQ (lookDT treeK) strsAll iv51.hi (iv51.p.getD 0 dPrm) (iv51.d.getD 0 [])) = true := by
  decide +kernel

theorem iv51_c1 : below iv51.lo (caseIIQ (lookDT treeK) admPre strsAll iv51.hi (iv51.p.getD 1 dPrm) (iv51.d.getD 1 [])) = true := by
  decide +kernel

theorem iv51_c2 : below iv51.lo (caseIII1Q (lookDT treeK) admPre strsAll iv51.hi (iv51.p.getD 2 dPrm) (iv51.d.getD 2 [])) = true := by
  decide +kernel

theorem iv51_c3 : below iv51.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv51.hi (iv51.p.getD 3 dPrm) (iv51.d.getD 3 [])) = true := by
  decide +kernel

theorem iv51_c4 : below iv51.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv51.hi (iv51.p.getD 4 dPrm) (iv51.d.getD 4 []) (iv51.d.getD 5 [])) = true := by
  decide +kernel

theorem iv51_ok : checkIv2 (lookDT treeK) admPre strsAll iv51 = true :=
  checkIv2_of_cases _ _ _ iv51 rfl rfl (by decide +kernel) iv51_c0 iv51_c1 iv51_c2 iv51_c3 iv51_c4

end ErdosComp
