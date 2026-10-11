import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv70_c0 : below iv70.lo (caseIbQ (lookDT treeK) strsAll iv70.hi (iv70.p.getD 0 dPrm) (iv70.d.getD 0 [])) = true := by
  decide +kernel

theorem iv70_c1 : below iv70.lo (caseIIQ (lookDT treeK) admPre strsAll iv70.hi (iv70.p.getD 1 dPrm) (iv70.d.getD 1 [])) = true := by
  decide +kernel

theorem iv70_c2 : below iv70.lo (caseIII1Q (lookDT treeK) admPre strsAll iv70.hi (iv70.p.getD 2 dPrm) (iv70.d.getD 2 [])) = true := by
  decide +kernel

theorem iv70_c3 : below iv70.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv70.hi (iv70.p.getD 3 dPrm) (iv70.d.getD 3 [])) = true := by
  decide +kernel

theorem iv70_c4 : below iv70.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv70.hi (iv70.p.getD 4 dPrm) (iv70.d.getD 4 []) (iv70.d.getD 5 [])) = true := by
  decide +kernel

theorem iv70_ok : checkIv2 (lookDT treeK) admPre strsAll iv70 = true :=
  checkIv2_of_cases _ _ _ iv70 rfl rfl (by decide +kernel) iv70_c0 iv70_c1 iv70_c2 iv70_c3 iv70_c4

end ErdosComp
