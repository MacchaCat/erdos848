import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv186_c0 : below iv186.lo (caseIbQ (lookDT treeK) strsAll iv186.hi (iv186.p.getD 0 dPrm) (iv186.d.getD 0 [])) = true := by
  decide +kernel

theorem iv186_c1 : below iv186.lo (caseIIQ (lookDT treeK) admPre strsAll iv186.hi (iv186.p.getD 1 dPrm) (iv186.d.getD 1 [])) = true := by
  decide +kernel

theorem iv186_c2 : below iv186.lo (caseIII1Q (lookDT treeK) admPre strsAll iv186.hi (iv186.p.getD 2 dPrm) (iv186.d.getD 2 [])) = true := by
  decide +kernel

theorem iv186_c3 : below iv186.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv186.hi (iv186.p.getD 3 dPrm) (iv186.d.getD 3 [])) = true := by
  decide +kernel

theorem iv186_c4 : below iv186.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv186.hi (iv186.p.getD 4 dPrm) (iv186.d.getD 4 []) (iv186.d.getD 5 [])) = true := by
  decide +kernel

theorem iv186_ok : checkIv2 (lookDT treeK) admPre strsAll iv186 = true :=
  checkIv2_of_cases _ _ _ iv186 rfl rfl (by decide +kernel) iv186_c0 iv186_c1 iv186_c2 iv186_c3 iv186_c4

end ErdosComp
