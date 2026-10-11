import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv77_c0 : below iv77.lo (caseIbQ (lookDT treeK) strsAll iv77.hi (iv77.p.getD 0 dPrm) (iv77.d.getD 0 [])) = true := by
  decide +kernel

theorem iv77_c1 : below iv77.lo (caseIIQ (lookDT treeK) admPre strsAll iv77.hi (iv77.p.getD 1 dPrm) (iv77.d.getD 1 [])) = true := by
  decide +kernel

theorem iv77_c2 : below iv77.lo (caseIII1Q (lookDT treeK) admPre strsAll iv77.hi (iv77.p.getD 2 dPrm) (iv77.d.getD 2 [])) = true := by
  decide +kernel

theorem iv77_c3 : below iv77.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv77.hi (iv77.p.getD 3 dPrm) (iv77.d.getD 3 [])) = true := by
  decide +kernel

theorem iv77_c4 : below iv77.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv77.hi (iv77.p.getD 4 dPrm) (iv77.d.getD 4 []) (iv77.d.getD 5 [])) = true := by
  decide +kernel

theorem iv77_ok : checkIv2 (lookDT treeK) admPre strsAll iv77 = true :=
  checkIv2_of_cases _ _ _ iv77 rfl rfl (by decide +kernel) iv77_c0 iv77_c1 iv77_c2 iv77_c3 iv77_c4

end ErdosComp
