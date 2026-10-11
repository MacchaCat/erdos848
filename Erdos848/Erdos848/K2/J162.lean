import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv162_c0 : below iv162.lo (caseIbQ (lookDT treeK) strsAll iv162.hi (iv162.p.getD 0 dPrm) (iv162.d.getD 0 [])) = true := by
  decide +kernel

theorem iv162_c1 : below iv162.lo (caseIIQ (lookDT treeK) admPre strsAll iv162.hi (iv162.p.getD 1 dPrm) (iv162.d.getD 1 [])) = true := by
  decide +kernel

theorem iv162_c2 : below iv162.lo (caseIII1Q (lookDT treeK) admPre strsAll iv162.hi (iv162.p.getD 2 dPrm) (iv162.d.getD 2 [])) = true := by
  decide +kernel

theorem iv162_c3 : below iv162.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv162.hi (iv162.p.getD 3 dPrm) (iv162.d.getD 3 [])) = true := by
  decide +kernel

theorem iv162_c4 : below iv162.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv162.hi (iv162.p.getD 4 dPrm) (iv162.d.getD 4 []) (iv162.d.getD 5 [])) = true := by
  decide +kernel

theorem iv162_ok : checkIv2 (lookDT treeK) admPre strsAll iv162 = true :=
  checkIv2_of_cases _ _ _ iv162 rfl rfl (by decide +kernel) iv162_c0 iv162_c1 iv162_c2 iv162_c3 iv162_c4

end ErdosComp
