import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv99_c0 : below iv99.lo (caseIbQ (lookDT treeK) strsAll iv99.hi (iv99.p.getD 0 dPrm) (iv99.d.getD 0 [])) = true := by
  decide +kernel

theorem iv99_c1 : below iv99.lo (caseIIQ (lookDT treeK) admPre strsAll iv99.hi (iv99.p.getD 1 dPrm) (iv99.d.getD 1 [])) = true := by
  decide +kernel

theorem iv99_c2 : below iv99.lo (caseIII1Q (lookDT treeK) admPre strsAll iv99.hi (iv99.p.getD 2 dPrm) (iv99.d.getD 2 [])) = true := by
  decide +kernel

theorem iv99_c3 : below iv99.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv99.hi (iv99.p.getD 3 dPrm) (iv99.d.getD 3 [])) = true := by
  decide +kernel

theorem iv99_c4 : below iv99.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv99.hi (iv99.p.getD 4 dPrm) (iv99.d.getD 4 []) (iv99.d.getD 5 [])) = true := by
  decide +kernel

theorem iv99_ok : checkIv2 (lookDT treeK) admPre strsAll iv99 = true :=
  checkIv2_of_cases _ _ _ iv99 rfl rfl (by decide +kernel) iv99_c0 iv99_c1 iv99_c2 iv99_c3 iv99_c4

end ErdosComp
