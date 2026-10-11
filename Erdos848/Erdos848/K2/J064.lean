import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv64_c0 : below iv64.lo (caseIbQ (lookDT treeK) strsAll iv64.hi (iv64.p.getD 0 dPrm) (iv64.d.getD 0 [])) = true := by
  decide +kernel

theorem iv64_c1 : below iv64.lo (caseIIQ (lookDT treeK) admPre strsAll iv64.hi (iv64.p.getD 1 dPrm) (iv64.d.getD 1 [])) = true := by
  decide +kernel

theorem iv64_c2 : below iv64.lo (caseIII1Q (lookDT treeK) admPre strsAll iv64.hi (iv64.p.getD 2 dPrm) (iv64.d.getD 2 [])) = true := by
  decide +kernel

theorem iv64_c3 : below iv64.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv64.hi (iv64.p.getD 3 dPrm) (iv64.d.getD 3 [])) = true := by
  decide +kernel

theorem iv64_c4 : below iv64.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv64.hi (iv64.p.getD 4 dPrm) (iv64.d.getD 4 []) (iv64.d.getD 5 [])) = true := by
  decide +kernel

theorem iv64_ok : checkIv2 (lookDT treeK) admPre strsAll iv64 = true :=
  checkIv2_of_cases _ _ _ iv64 rfl rfl (by decide +kernel) iv64_c0 iv64_c1 iv64_c2 iv64_c3 iv64_c4

end ErdosComp
