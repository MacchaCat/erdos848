import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv132_c0 : below iv132.lo (caseIbQ (lookDT treeK) strsAll iv132.hi (iv132.p.getD 0 dPrm) (iv132.d.getD 0 [])) = true := by
  decide +kernel

theorem iv132_c1 : below iv132.lo (caseIIQ (lookDT treeK) admPre strsAll iv132.hi (iv132.p.getD 1 dPrm) (iv132.d.getD 1 [])) = true := by
  decide +kernel

theorem iv132_c2 : below iv132.lo (caseIII1Q (lookDT treeK) admPre strsAll iv132.hi (iv132.p.getD 2 dPrm) (iv132.d.getD 2 [])) = true := by
  decide +kernel

theorem iv132_c3 : below iv132.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv132.hi (iv132.p.getD 3 dPrm) (iv132.d.getD 3 [])) = true := by
  decide +kernel

theorem iv132_c4 : below iv132.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv132.hi (iv132.p.getD 4 dPrm) (iv132.d.getD 4 []) (iv132.d.getD 5 [])) = true := by
  decide +kernel

theorem iv132_ok : checkIv2 (lookDT treeK) admPre strsAll iv132 = true :=
  checkIv2_of_cases _ _ _ iv132 rfl rfl (by decide +kernel) iv132_c0 iv132_c1 iv132_c2 iv132_c3 iv132_c4

end ErdosComp
