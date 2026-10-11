import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv192_c0 : below iv192.lo (caseIbQ (lookDT treeK) strsAll iv192.hi (iv192.p.getD 0 dPrm) (iv192.d.getD 0 [])) = true := by
  decide +kernel

theorem iv192_c1 : below iv192.lo (caseIIQ (lookDT treeK) admPre strsAll iv192.hi (iv192.p.getD 1 dPrm) (iv192.d.getD 1 [])) = true := by
  decide +kernel

theorem iv192_c2 : below iv192.lo (caseIII1Q (lookDT treeK) admPre strsAll iv192.hi (iv192.p.getD 2 dPrm) (iv192.d.getD 2 [])) = true := by
  decide +kernel

theorem iv192_c3 : below iv192.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv192.hi (iv192.p.getD 3 dPrm) (iv192.d.getD 3 [])) = true := by
  decide +kernel

theorem iv192_c4 : below iv192.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv192.hi (iv192.p.getD 4 dPrm) (iv192.d.getD 4 []) (iv192.d.getD 5 [])) = true := by
  decide +kernel

theorem iv192_ok : checkIv2 (lookDT treeK) admPre strsAll iv192 = true :=
  checkIv2_of_cases _ _ _ iv192 rfl rfl (by decide +kernel) iv192_c0 iv192_c1 iv192_c2 iv192_c3 iv192_c4

end ErdosComp
