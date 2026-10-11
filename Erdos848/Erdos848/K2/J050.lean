import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv50_c0 : below iv50.lo (caseIbQ (lookDT treeK) strsAll iv50.hi (iv50.p.getD 0 dPrm) (iv50.d.getD 0 [])) = true := by
  decide +kernel

theorem iv50_c1 : below iv50.lo (caseIIQ (lookDT treeK) admPre strsAll iv50.hi (iv50.p.getD 1 dPrm) (iv50.d.getD 1 [])) = true := by
  decide +kernel

theorem iv50_c2 : below iv50.lo (caseIII1Q (lookDT treeK) admPre strsAll iv50.hi (iv50.p.getD 2 dPrm) (iv50.d.getD 2 [])) = true := by
  decide +kernel

theorem iv50_c3 : below iv50.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv50.hi (iv50.p.getD 3 dPrm) (iv50.d.getD 3 [])) = true := by
  decide +kernel

theorem iv50_c4 : below iv50.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv50.hi (iv50.p.getD 4 dPrm) (iv50.d.getD 4 []) (iv50.d.getD 5 [])) = true := by
  decide +kernel

theorem iv50_ok : checkIv2 (lookDT treeK) admPre strsAll iv50 = true :=
  checkIv2_of_cases _ _ _ iv50 rfl rfl (by decide +kernel) iv50_c0 iv50_c1 iv50_c2 iv50_c3 iv50_c4

end ErdosComp
