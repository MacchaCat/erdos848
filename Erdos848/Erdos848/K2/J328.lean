import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv328_c0 : below iv328.lo (caseIbQ (lookDT treeK) strsAll iv328.hi (iv328.p.getD 0 dPrm) (iv328.d.getD 0 [])) = true := by
  decide +kernel

theorem iv328_c1 : below iv328.lo (caseIIQ (lookDT treeK) admPre strsAll iv328.hi (iv328.p.getD 1 dPrm) (iv328.d.getD 1 [])) = true := by
  decide +kernel

theorem iv328_c2 : below iv328.lo (caseIII1Q (lookDT treeK) admPre strsAll iv328.hi (iv328.p.getD 2 dPrm) (iv328.d.getD 2 [])) = true := by
  decide +kernel

theorem iv328_c3 : below iv328.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv328.hi (iv328.p.getD 3 dPrm) (iv328.d.getD 3 [])) = true := by
  decide +kernel

theorem iv328_c4 : below iv328.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv328.hi (iv328.p.getD 4 dPrm) (iv328.d.getD 4 []) (iv328.d.getD 5 [])) = true := by
  decide +kernel

theorem iv328_ok : checkIv2 (lookDT treeK) admPre strsAll iv328 = true :=
  checkIv2_of_cases _ _ _ iv328 rfl rfl (by decide +kernel) iv328_c0 iv328_c1 iv328_c2 iv328_c3 iv328_c4

end ErdosComp
