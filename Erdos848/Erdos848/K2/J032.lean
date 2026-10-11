import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv32_c0 : below iv32.lo (caseIbQ (lookDT treeK) strsAll iv32.hi (iv32.p.getD 0 dPrm) (iv32.d.getD 0 [])) = true := by
  decide +kernel

theorem iv32_c1 : below iv32.lo (caseIIQ (lookDT treeK) admPre strsAll iv32.hi (iv32.p.getD 1 dPrm) (iv32.d.getD 1 [])) = true := by
  decide +kernel

theorem iv32_c2 : below iv32.lo (caseIII1Q (lookDT treeK) admPre strsAll iv32.hi (iv32.p.getD 2 dPrm) (iv32.d.getD 2 [])) = true := by
  decide +kernel

theorem iv32_c3 : below iv32.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv32.hi (iv32.p.getD 3 dPrm) (iv32.d.getD 3 [])) = true := by
  decide +kernel

theorem iv32_c4 : below iv32.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv32.hi (iv32.p.getD 4 dPrm) (iv32.d.getD 4 []) (iv32.d.getD 5 [])) = true := by
  decide +kernel

theorem iv32_ok : checkIv2 (lookDT treeK) admPre strsAll iv32 = true :=
  checkIv2_of_cases _ _ _ iv32 rfl rfl (by decide +kernel) iv32_c0 iv32_c1 iv32_c2 iv32_c3 iv32_c4

end ErdosComp
