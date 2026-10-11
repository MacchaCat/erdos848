import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv97_c0 : below iv97.lo (caseIbQ (lookDT treeK) strsAll iv97.hi (iv97.p.getD 0 dPrm) (iv97.d.getD 0 [])) = true := by
  decide +kernel

theorem iv97_c1 : below iv97.lo (caseIIQ (lookDT treeK) admPre strsAll iv97.hi (iv97.p.getD 1 dPrm) (iv97.d.getD 1 [])) = true := by
  decide +kernel

theorem iv97_c2 : below iv97.lo (caseIII1Q (lookDT treeK) admPre strsAll iv97.hi (iv97.p.getD 2 dPrm) (iv97.d.getD 2 [])) = true := by
  decide +kernel

theorem iv97_c3 : below iv97.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv97.hi (iv97.p.getD 3 dPrm) (iv97.d.getD 3 [])) = true := by
  decide +kernel

theorem iv97_c4 : below iv97.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv97.hi (iv97.p.getD 4 dPrm) (iv97.d.getD 4 []) (iv97.d.getD 5 [])) = true := by
  decide +kernel

theorem iv97_ok : checkIv2 (lookDT treeK) admPre strsAll iv97 = true :=
  checkIv2_of_cases _ _ _ iv97 rfl rfl (by decide +kernel) iv97_c0 iv97_c1 iv97_c2 iv97_c3 iv97_c4

end ErdosComp
