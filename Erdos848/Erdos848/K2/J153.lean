import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv153_c0 : below iv153.lo (caseIbQ (lookDT treeK) strsAll iv153.hi (iv153.p.getD 0 dPrm) (iv153.d.getD 0 [])) = true := by
  decide +kernel

theorem iv153_c1 : below iv153.lo (caseIIQ (lookDT treeK) admPre strsAll iv153.hi (iv153.p.getD 1 dPrm) (iv153.d.getD 1 [])) = true := by
  decide +kernel

theorem iv153_c2 : below iv153.lo (caseIII1Q (lookDT treeK) admPre strsAll iv153.hi (iv153.p.getD 2 dPrm) (iv153.d.getD 2 [])) = true := by
  decide +kernel

theorem iv153_c3 : below iv153.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv153.hi (iv153.p.getD 3 dPrm) (iv153.d.getD 3 [])) = true := by
  decide +kernel

theorem iv153_c4 : below iv153.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv153.hi (iv153.p.getD 4 dPrm) (iv153.d.getD 4 []) (iv153.d.getD 5 [])) = true := by
  decide +kernel

theorem iv153_ok : checkIv2 (lookDT treeK) admPre strsAll iv153 = true :=
  checkIv2_of_cases _ _ _ iv153 rfl rfl (by decide +kernel) iv153_c0 iv153_c1 iv153_c2 iv153_c3 iv153_c4

end ErdosComp
