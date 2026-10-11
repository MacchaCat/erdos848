import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv122_c0 : below iv122.lo (caseIbQ (lookDT treeK) strsAll iv122.hi (iv122.p.getD 0 dPrm) (iv122.d.getD 0 [])) = true := by
  decide +kernel

theorem iv122_c1 : below iv122.lo (caseIIQ (lookDT treeK) admPre strsAll iv122.hi (iv122.p.getD 1 dPrm) (iv122.d.getD 1 [])) = true := by
  decide +kernel

theorem iv122_c2 : below iv122.lo (caseIII1Q (lookDT treeK) admPre strsAll iv122.hi (iv122.p.getD 2 dPrm) (iv122.d.getD 2 [])) = true := by
  decide +kernel

theorem iv122_c3 : below iv122.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv122.hi (iv122.p.getD 3 dPrm) (iv122.d.getD 3 [])) = true := by
  decide +kernel

theorem iv122_c4 : below iv122.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv122.hi (iv122.p.getD 4 dPrm) (iv122.d.getD 4 []) (iv122.d.getD 5 [])) = true := by
  decide +kernel

theorem iv122_ok : checkIv2 (lookDT treeK) admPre strsAll iv122 = true :=
  checkIv2_of_cases _ _ _ iv122 rfl rfl (by decide +kernel) iv122_c0 iv122_c1 iv122_c2 iv122_c3 iv122_c4

end ErdosComp
