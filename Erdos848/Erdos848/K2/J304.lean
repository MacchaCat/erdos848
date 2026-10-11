import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv304_c0 : below iv304.lo (caseIbQ (lookDT treeK) strsAll iv304.hi (iv304.p.getD 0 dPrm) (iv304.d.getD 0 [])) = true := by
  decide +kernel

theorem iv304_c1 : below iv304.lo (caseIIQ (lookDT treeK) admPre strsAll iv304.hi (iv304.p.getD 1 dPrm) (iv304.d.getD 1 [])) = true := by
  decide +kernel

theorem iv304_c2 : below iv304.lo (caseIII1Q (lookDT treeK) admPre strsAll iv304.hi (iv304.p.getD 2 dPrm) (iv304.d.getD 2 [])) = true := by
  decide +kernel

theorem iv304_c3 : below iv304.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv304.hi (iv304.p.getD 3 dPrm) (iv304.d.getD 3 [])) = true := by
  decide +kernel

theorem iv304_c4 : below iv304.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv304.hi (iv304.p.getD 4 dPrm) (iv304.d.getD 4 []) (iv304.d.getD 5 [])) = true := by
  decide +kernel

theorem iv304_ok : checkIv2 (lookDT treeK) admPre strsAll iv304 = true :=
  checkIv2_of_cases _ _ _ iv304 rfl rfl (by decide +kernel) iv304_c0 iv304_c1 iv304_c2 iv304_c3 iv304_c4

end ErdosComp
