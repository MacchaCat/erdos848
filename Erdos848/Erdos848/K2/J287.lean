import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv287_c0 : below iv287.lo (caseIbQ (lookDT treeK) strsAll iv287.hi (iv287.p.getD 0 dPrm) (iv287.d.getD 0 [])) = true := by
  decide +kernel

theorem iv287_c1 : below iv287.lo (caseIIQ (lookDT treeK) admPre strsAll iv287.hi (iv287.p.getD 1 dPrm) (iv287.d.getD 1 [])) = true := by
  decide +kernel

theorem iv287_c2 : below iv287.lo (caseIII1Q (lookDT treeK) admPre strsAll iv287.hi (iv287.p.getD 2 dPrm) (iv287.d.getD 2 [])) = true := by
  decide +kernel

theorem iv287_c3 : below iv287.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv287.hi (iv287.p.getD 3 dPrm) (iv287.d.getD 3 [])) = true := by
  decide +kernel

theorem iv287_c4 : below iv287.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv287.hi (iv287.p.getD 4 dPrm) (iv287.d.getD 4 []) (iv287.d.getD 5 [])) = true := by
  decide +kernel

theorem iv287_ok : checkIv2 (lookDT treeK) admPre strsAll iv287 = true :=
  checkIv2_of_cases _ _ _ iv287 rfl rfl (by decide +kernel) iv287_c0 iv287_c1 iv287_c2 iv287_c3 iv287_c4

end ErdosComp
