import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv292_c0 : below iv292.lo (caseIbQ (lookDT treeK) strsAll iv292.hi (iv292.p.getD 0 dPrm) (iv292.d.getD 0 [])) = true := by
  decide +kernel

theorem iv292_c1 : below iv292.lo (caseIIQ (lookDT treeK) admPre strsAll iv292.hi (iv292.p.getD 1 dPrm) (iv292.d.getD 1 [])) = true := by
  decide +kernel

theorem iv292_c2 : below iv292.lo (caseIII1Q (lookDT treeK) admPre strsAll iv292.hi (iv292.p.getD 2 dPrm) (iv292.d.getD 2 [])) = true := by
  decide +kernel

theorem iv292_c3 : below iv292.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv292.hi (iv292.p.getD 3 dPrm) (iv292.d.getD 3 [])) = true := by
  decide +kernel

theorem iv292_c4 : below iv292.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv292.hi (iv292.p.getD 4 dPrm) (iv292.d.getD 4 []) (iv292.d.getD 5 [])) = true := by
  decide +kernel

theorem iv292_ok : checkIv2 (lookDT treeK) admPre strsAll iv292 = true :=
  checkIv2_of_cases _ _ _ iv292 rfl rfl (by decide +kernel) iv292_c0 iv292_c1 iv292_c2 iv292_c3 iv292_c4

end ErdosComp
