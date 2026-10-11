import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv263_c0 : below iv263.lo (caseIbQ (lookDT treeK) strsAll iv263.hi (iv263.p.getD 0 dPrm) (iv263.d.getD 0 [])) = true := by
  decide +kernel

theorem iv263_c1 : below iv263.lo (caseIIQ (lookDT treeK) admPre strsAll iv263.hi (iv263.p.getD 1 dPrm) (iv263.d.getD 1 [])) = true := by
  decide +kernel

theorem iv263_c2 : below iv263.lo (caseIII1Q (lookDT treeK) admPre strsAll iv263.hi (iv263.p.getD 2 dPrm) (iv263.d.getD 2 [])) = true := by
  decide +kernel

theorem iv263_c3 : below iv263.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv263.hi (iv263.p.getD 3 dPrm) (iv263.d.getD 3 [])) = true := by
  decide +kernel

theorem iv263_c4 : below iv263.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv263.hi (iv263.p.getD 4 dPrm) (iv263.d.getD 4 []) (iv263.d.getD 5 [])) = true := by
  decide +kernel

theorem iv263_ok : checkIv2 (lookDT treeK) admPre strsAll iv263 = true :=
  checkIv2_of_cases _ _ _ iv263 rfl rfl (by decide +kernel) iv263_c0 iv263_c1 iv263_c2 iv263_c3 iv263_c4

end ErdosComp
