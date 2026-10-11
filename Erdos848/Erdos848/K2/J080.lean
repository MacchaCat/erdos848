import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv80_c0 : below iv80.lo (caseIbQ (lookDT treeK) strsAll iv80.hi (iv80.p.getD 0 dPrm) (iv80.d.getD 0 [])) = true := by
  decide +kernel

theorem iv80_c1 : below iv80.lo (caseIIQ (lookDT treeK) admPre strsAll iv80.hi (iv80.p.getD 1 dPrm) (iv80.d.getD 1 [])) = true := by
  decide +kernel

theorem iv80_c2 : below iv80.lo (caseIII1Q (lookDT treeK) admPre strsAll iv80.hi (iv80.p.getD 2 dPrm) (iv80.d.getD 2 [])) = true := by
  decide +kernel

theorem iv80_c3 : below iv80.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv80.hi (iv80.p.getD 3 dPrm) (iv80.d.getD 3 [])) = true := by
  decide +kernel

theorem iv80_c4 : below iv80.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv80.hi (iv80.p.getD 4 dPrm) (iv80.d.getD 4 []) (iv80.d.getD 5 [])) = true := by
  decide +kernel

theorem iv80_ok : checkIv2 (lookDT treeK) admPre strsAll iv80 = true :=
  checkIv2_of_cases _ _ _ iv80 rfl rfl (by decide +kernel) iv80_c0 iv80_c1 iv80_c2 iv80_c3 iv80_c4

end ErdosComp
