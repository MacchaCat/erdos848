import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv169_c0 : below iv169.lo (caseIbQ (lookDT treeK) strsAll iv169.hi (iv169.p.getD 0 dPrm) (iv169.d.getD 0 [])) = true := by
  decide +kernel

theorem iv169_c1 : below iv169.lo (caseIIQ (lookDT treeK) admPre strsAll iv169.hi (iv169.p.getD 1 dPrm) (iv169.d.getD 1 [])) = true := by
  decide +kernel

theorem iv169_c2 : below iv169.lo (caseIII1Q (lookDT treeK) admPre strsAll iv169.hi (iv169.p.getD 2 dPrm) (iv169.d.getD 2 [])) = true := by
  decide +kernel

theorem iv169_c3 : below iv169.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv169.hi (iv169.p.getD 3 dPrm) (iv169.d.getD 3 [])) = true := by
  decide +kernel

theorem iv169_c4 : below iv169.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv169.hi (iv169.p.getD 4 dPrm) (iv169.d.getD 4 []) (iv169.d.getD 5 [])) = true := by
  decide +kernel

theorem iv169_ok : checkIv2 (lookDT treeK) admPre strsAll iv169 = true :=
  checkIv2_of_cases _ _ _ iv169 rfl rfl (by decide +kernel) iv169_c0 iv169_c1 iv169_c2 iv169_c3 iv169_c4

end ErdosComp
