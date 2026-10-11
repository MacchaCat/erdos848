import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv305_c0 : below iv305.lo (caseIbQ (lookDT treeK) strsAll iv305.hi (iv305.p.getD 0 dPrm) (iv305.d.getD 0 [])) = true := by
  decide +kernel

theorem iv305_c1 : below iv305.lo (caseIIQ (lookDT treeK) admPre strsAll iv305.hi (iv305.p.getD 1 dPrm) (iv305.d.getD 1 [])) = true := by
  decide +kernel

theorem iv305_c2 : below iv305.lo (caseIII1Q (lookDT treeK) admPre strsAll iv305.hi (iv305.p.getD 2 dPrm) (iv305.d.getD 2 [])) = true := by
  decide +kernel

theorem iv305_c3 : below iv305.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv305.hi (iv305.p.getD 3 dPrm) (iv305.d.getD 3 [])) = true := by
  decide +kernel

theorem iv305_c4 : below iv305.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv305.hi (iv305.p.getD 4 dPrm) (iv305.d.getD 4 []) (iv305.d.getD 5 [])) = true := by
  decide +kernel

theorem iv305_ok : checkIv2 (lookDT treeK) admPre strsAll iv305 = true :=
  checkIv2_of_cases _ _ _ iv305 rfl rfl (by decide +kernel) iv305_c0 iv305_c1 iv305_c2 iv305_c3 iv305_c4

end ErdosComp
