import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv174_c0 : below iv174.lo (caseIbQ (lookDT treeK) strsAll iv174.hi (iv174.p.getD 0 dPrm) (iv174.d.getD 0 [])) = true := by
  decide +kernel

theorem iv174_c1 : below iv174.lo (caseIIQ (lookDT treeK) admPre strsAll iv174.hi (iv174.p.getD 1 dPrm) (iv174.d.getD 1 [])) = true := by
  decide +kernel

theorem iv174_c2 : below iv174.lo (caseIII1Q (lookDT treeK) admPre strsAll iv174.hi (iv174.p.getD 2 dPrm) (iv174.d.getD 2 [])) = true := by
  decide +kernel

theorem iv174_c3 : below iv174.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv174.hi (iv174.p.getD 3 dPrm) (iv174.d.getD 3 [])) = true := by
  decide +kernel

theorem iv174_c4 : below iv174.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv174.hi (iv174.p.getD 4 dPrm) (iv174.d.getD 4 []) (iv174.d.getD 5 [])) = true := by
  decide +kernel

theorem iv174_ok : checkIv2 (lookDT treeK) admPre strsAll iv174 = true :=
  checkIv2_of_cases _ _ _ iv174 rfl rfl (by decide +kernel) iv174_c0 iv174_c1 iv174_c2 iv174_c3 iv174_c4

end ErdosComp
