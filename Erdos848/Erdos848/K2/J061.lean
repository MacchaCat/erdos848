import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv61_c0 : below iv61.lo (caseIbQ (lookDT treeK) strsAll iv61.hi (iv61.p.getD 0 dPrm) (iv61.d.getD 0 [])) = true := by
  decide +kernel

theorem iv61_c1 : below iv61.lo (caseIIQ (lookDT treeK) admPre strsAll iv61.hi (iv61.p.getD 1 dPrm) (iv61.d.getD 1 [])) = true := by
  decide +kernel

theorem iv61_c2 : below iv61.lo (caseIII1Q (lookDT treeK) admPre strsAll iv61.hi (iv61.p.getD 2 dPrm) (iv61.d.getD 2 [])) = true := by
  decide +kernel

theorem iv61_c3 : below iv61.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv61.hi (iv61.p.getD 3 dPrm) (iv61.d.getD 3 [])) = true := by
  decide +kernel

theorem iv61_c4 : below iv61.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv61.hi (iv61.p.getD 4 dPrm) (iv61.d.getD 4 []) (iv61.d.getD 5 [])) = true := by
  decide +kernel

theorem iv61_ok : checkIv2 (lookDT treeK) admPre strsAll iv61 = true :=
  checkIv2_of_cases _ _ _ iv61 rfl rfl (by decide +kernel) iv61_c0 iv61_c1 iv61_c2 iv61_c3 iv61_c4

end ErdosComp
