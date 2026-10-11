import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv68_c0 : below iv68.lo (caseIbQ (lookDT treeK) strsAll iv68.hi (iv68.p.getD 0 dPrm) (iv68.d.getD 0 [])) = true := by
  decide +kernel

theorem iv68_c1 : below iv68.lo (caseIIQ (lookDT treeK) admPre strsAll iv68.hi (iv68.p.getD 1 dPrm) (iv68.d.getD 1 [])) = true := by
  decide +kernel

theorem iv68_c2 : below iv68.lo (caseIII1Q (lookDT treeK) admPre strsAll iv68.hi (iv68.p.getD 2 dPrm) (iv68.d.getD 2 [])) = true := by
  decide +kernel

theorem iv68_c3 : below iv68.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv68.hi (iv68.p.getD 3 dPrm) (iv68.d.getD 3 [])) = true := by
  decide +kernel

theorem iv68_c4 : below iv68.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv68.hi (iv68.p.getD 4 dPrm) (iv68.d.getD 4 []) (iv68.d.getD 5 [])) = true := by
  decide +kernel

theorem iv68_ok : checkIv2 (lookDT treeK) admPre strsAll iv68 = true :=
  checkIv2_of_cases _ _ _ iv68 rfl rfl (by decide +kernel) iv68_c0 iv68_c1 iv68_c2 iv68_c3 iv68_c4

end ErdosComp
