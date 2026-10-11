import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv325_c0 : below iv325.lo (caseIbQ (lookDT treeK) strsAll iv325.hi (iv325.p.getD 0 dPrm) (iv325.d.getD 0 [])) = true := by
  decide +kernel

theorem iv325_c1 : below iv325.lo (caseIIQ (lookDT treeK) admPre strsAll iv325.hi (iv325.p.getD 1 dPrm) (iv325.d.getD 1 [])) = true := by
  decide +kernel

theorem iv325_c2 : below iv325.lo (caseIII1Q (lookDT treeK) admPre strsAll iv325.hi (iv325.p.getD 2 dPrm) (iv325.d.getD 2 [])) = true := by
  decide +kernel

theorem iv325_c3 : below iv325.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv325.hi (iv325.p.getD 3 dPrm) (iv325.d.getD 3 [])) = true := by
  decide +kernel

theorem iv325_c4 : below iv325.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv325.hi (iv325.p.getD 4 dPrm) (iv325.d.getD 4 []) (iv325.d.getD 5 [])) = true := by
  decide +kernel

theorem iv325_ok : checkIv2 (lookDT treeK) admPre strsAll iv325 = true :=
  checkIv2_of_cases _ _ _ iv325 rfl rfl (by decide +kernel) iv325_c0 iv325_c1 iv325_c2 iv325_c3 iv325_c4

end ErdosComp
