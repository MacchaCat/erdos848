import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv41_c0 : below iv41.lo (caseIbQ (lookDT treeK) strsAll iv41.hi (iv41.p.getD 0 dPrm) (iv41.d.getD 0 [])) = true := by
  decide +kernel

theorem iv41_c1 : below iv41.lo (caseIIQ (lookDT treeK) admPre strsAll iv41.hi (iv41.p.getD 1 dPrm) (iv41.d.getD 1 [])) = true := by
  decide +kernel

theorem iv41_c2 : below iv41.lo (caseIII1Q (lookDT treeK) admPre strsAll iv41.hi (iv41.p.getD 2 dPrm) (iv41.d.getD 2 [])) = true := by
  decide +kernel

theorem iv41_c3 : below iv41.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv41.hi (iv41.p.getD 3 dPrm) (iv41.d.getD 3 [])) = true := by
  decide +kernel

theorem iv41_c4 : below iv41.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv41.hi (iv41.p.getD 4 dPrm) (iv41.d.getD 4 []) (iv41.d.getD 5 [])) = true := by
  decide +kernel

theorem iv41_ok : checkIv2 (lookDT treeK) admPre strsAll iv41 = true :=
  checkIv2_of_cases _ _ _ iv41 rfl rfl (by decide +kernel) iv41_c0 iv41_c1 iv41_c2 iv41_c3 iv41_c4

end ErdosComp
