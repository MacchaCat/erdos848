import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv267_c0 : below iv267.lo (caseIbQ (lookDT treeK) strsAll iv267.hi (iv267.p.getD 0 dPrm) (iv267.d.getD 0 [])) = true := by
  decide +kernel

theorem iv267_c1 : below iv267.lo (caseIIQ (lookDT treeK) admPre strsAll iv267.hi (iv267.p.getD 1 dPrm) (iv267.d.getD 1 [])) = true := by
  decide +kernel

theorem iv267_c2 : below iv267.lo (caseIII1Q (lookDT treeK) admPre strsAll iv267.hi (iv267.p.getD 2 dPrm) (iv267.d.getD 2 [])) = true := by
  decide +kernel

theorem iv267_c3 : below iv267.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv267.hi (iv267.p.getD 3 dPrm) (iv267.d.getD 3 [])) = true := by
  decide +kernel

theorem iv267_c4 : below iv267.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv267.hi (iv267.p.getD 4 dPrm) (iv267.d.getD 4 []) (iv267.d.getD 5 [])) = true := by
  decide +kernel

theorem iv267_ok : checkIv2 (lookDT treeK) admPre strsAll iv267 = true :=
  checkIv2_of_cases _ _ _ iv267 rfl rfl (by decide +kernel) iv267_c0 iv267_c1 iv267_c2 iv267_c3 iv267_c4

end ErdosComp
