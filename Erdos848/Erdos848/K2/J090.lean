import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv90_c0 : below iv90.lo (caseIbQ (lookDT treeK) strsAll iv90.hi (iv90.p.getD 0 dPrm) (iv90.d.getD 0 [])) = true := by
  decide +kernel

theorem iv90_c1 : below iv90.lo (caseIIQ (lookDT treeK) admPre strsAll iv90.hi (iv90.p.getD 1 dPrm) (iv90.d.getD 1 [])) = true := by
  decide +kernel

theorem iv90_c2 : below iv90.lo (caseIII1Q (lookDT treeK) admPre strsAll iv90.hi (iv90.p.getD 2 dPrm) (iv90.d.getD 2 [])) = true := by
  decide +kernel

theorem iv90_c3 : below iv90.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv90.hi (iv90.p.getD 3 dPrm) (iv90.d.getD 3 [])) = true := by
  decide +kernel

theorem iv90_c4 : below iv90.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv90.hi (iv90.p.getD 4 dPrm) (iv90.d.getD 4 []) (iv90.d.getD 5 [])) = true := by
  decide +kernel

theorem iv90_ok : checkIv2 (lookDT treeK) admPre strsAll iv90 = true :=
  checkIv2_of_cases _ _ _ iv90 rfl rfl (by decide +kernel) iv90_c0 iv90_c1 iv90_c2 iv90_c3 iv90_c4

end ErdosComp
