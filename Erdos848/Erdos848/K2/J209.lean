import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv209_c0 : below iv209.lo (caseIbQ (lookDT treeK) strsAll iv209.hi (iv209.p.getD 0 dPrm) (iv209.d.getD 0 [])) = true := by
  decide +kernel

theorem iv209_c1 : below iv209.lo (caseIIQ (lookDT treeK) admPre strsAll iv209.hi (iv209.p.getD 1 dPrm) (iv209.d.getD 1 [])) = true := by
  decide +kernel

theorem iv209_c2 : below iv209.lo (caseIII1Q (lookDT treeK) admPre strsAll iv209.hi (iv209.p.getD 2 dPrm) (iv209.d.getD 2 [])) = true := by
  decide +kernel

theorem iv209_c3 : below iv209.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv209.hi (iv209.p.getD 3 dPrm) (iv209.d.getD 3 [])) = true := by
  decide +kernel

theorem iv209_c4 : below iv209.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv209.hi (iv209.p.getD 4 dPrm) (iv209.d.getD 4 []) (iv209.d.getD 5 [])) = true := by
  decide +kernel

theorem iv209_ok : checkIv2 (lookDT treeK) admPre strsAll iv209 = true :=
  checkIv2_of_cases _ _ _ iv209 rfl rfl (by decide +kernel) iv209_c0 iv209_c1 iv209_c2 iv209_c3 iv209_c4

end ErdosComp
