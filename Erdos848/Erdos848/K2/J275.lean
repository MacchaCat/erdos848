import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv275_c0 : below iv275.lo (caseIbQ (lookDT treeK) strsAll iv275.hi (iv275.p.getD 0 dPrm) (iv275.d.getD 0 [])) = true := by
  decide +kernel

theorem iv275_c1 : below iv275.lo (caseIIQ (lookDT treeK) admPre strsAll iv275.hi (iv275.p.getD 1 dPrm) (iv275.d.getD 1 [])) = true := by
  decide +kernel

theorem iv275_c2 : below iv275.lo (caseIII1Q (lookDT treeK) admPre strsAll iv275.hi (iv275.p.getD 2 dPrm) (iv275.d.getD 2 [])) = true := by
  decide +kernel

theorem iv275_c3 : below iv275.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv275.hi (iv275.p.getD 3 dPrm) (iv275.d.getD 3 [])) = true := by
  decide +kernel

theorem iv275_c4 : below iv275.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv275.hi (iv275.p.getD 4 dPrm) (iv275.d.getD 4 []) (iv275.d.getD 5 [])) = true := by
  decide +kernel

theorem iv275_ok : checkIv2 (lookDT treeK) admPre strsAll iv275 = true :=
  checkIv2_of_cases _ _ _ iv275 rfl rfl (by decide +kernel) iv275_c0 iv275_c1 iv275_c2 iv275_c3 iv275_c4

end ErdosComp
