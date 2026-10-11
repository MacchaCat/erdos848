import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv342_c0 : below iv342.lo (caseIbQ (lookDT treeK) strsAll iv342.hi (iv342.p.getD 0 dPrm) (iv342.d.getD 0 [])) = true := by
  decide +kernel

theorem iv342_c1 : below iv342.lo (caseIIQ (lookDT treeK) admPre strsAll iv342.hi (iv342.p.getD 1 dPrm) (iv342.d.getD 1 [])) = true := by
  decide +kernel

theorem iv342_c2 : below iv342.lo (caseIII1Q (lookDT treeK) admPre strsAll iv342.hi (iv342.p.getD 2 dPrm) (iv342.d.getD 2 [])) = true := by
  decide +kernel

theorem iv342_c3 : below iv342.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv342.hi (iv342.p.getD 3 dPrm) (iv342.d.getD 3 [])) = true := by
  decide +kernel

theorem iv342_c4 : below iv342.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv342.hi (iv342.p.getD 4 dPrm) (iv342.d.getD 4 []) (iv342.d.getD 5 [])) = true := by
  decide +kernel

theorem iv342_ok : checkIv2 (lookDT treeK) admPre strsAll iv342 = true :=
  checkIv2_of_cases _ _ _ iv342 rfl rfl (by decide +kernel) iv342_c0 iv342_c1 iv342_c2 iv342_c3 iv342_c4

end ErdosComp
