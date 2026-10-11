import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv200_c0 : below iv200.lo (caseIbQ (lookDT treeK) strsAll iv200.hi (iv200.p.getD 0 dPrm) (iv200.d.getD 0 [])) = true := by
  decide +kernel

theorem iv200_c1 : below iv200.lo (caseIIQ (lookDT treeK) admPre strsAll iv200.hi (iv200.p.getD 1 dPrm) (iv200.d.getD 1 [])) = true := by
  decide +kernel

theorem iv200_c2 : below iv200.lo (caseIII1Q (lookDT treeK) admPre strsAll iv200.hi (iv200.p.getD 2 dPrm) (iv200.d.getD 2 [])) = true := by
  decide +kernel

theorem iv200_c3 : below iv200.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv200.hi (iv200.p.getD 3 dPrm) (iv200.d.getD 3 [])) = true := by
  decide +kernel

theorem iv200_c4 : below iv200.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv200.hi (iv200.p.getD 4 dPrm) (iv200.d.getD 4 []) (iv200.d.getD 5 [])) = true := by
  decide +kernel

theorem iv200_ok : checkIv2 (lookDT treeK) admPre strsAll iv200 = true :=
  checkIv2_of_cases _ _ _ iv200 rfl rfl (by decide +kernel) iv200_c0 iv200_c1 iv200_c2 iv200_c3 iv200_c4

end ErdosComp
