import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv138_c0 : below iv138.lo (caseIbQ (lookDT treeK) strsAll iv138.hi (iv138.p.getD 0 dPrm) (iv138.d.getD 0 [])) = true := by
  decide +kernel

theorem iv138_c1 : below iv138.lo (caseIIQ (lookDT treeK) admPre strsAll iv138.hi (iv138.p.getD 1 dPrm) (iv138.d.getD 1 [])) = true := by
  decide +kernel

theorem iv138_c2 : below iv138.lo (caseIII1Q (lookDT treeK) admPre strsAll iv138.hi (iv138.p.getD 2 dPrm) (iv138.d.getD 2 [])) = true := by
  decide +kernel

theorem iv138_c3 : below iv138.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv138.hi (iv138.p.getD 3 dPrm) (iv138.d.getD 3 [])) = true := by
  decide +kernel

theorem iv138_c4 : below iv138.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv138.hi (iv138.p.getD 4 dPrm) (iv138.d.getD 4 []) (iv138.d.getD 5 [])) = true := by
  decide +kernel

theorem iv138_ok : checkIv2 (lookDT treeK) admPre strsAll iv138 = true :=
  checkIv2_of_cases _ _ _ iv138 rfl rfl (by decide +kernel) iv138_c0 iv138_c1 iv138_c2 iv138_c3 iv138_c4

end ErdosComp
