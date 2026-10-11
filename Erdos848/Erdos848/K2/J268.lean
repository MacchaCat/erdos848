import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv268_c0 : below iv268.lo (caseIbQ (lookDT treeK) strsAll iv268.hi (iv268.p.getD 0 dPrm) (iv268.d.getD 0 [])) = true := by
  decide +kernel

theorem iv268_c1 : below iv268.lo (caseIIQ (lookDT treeK) admPre strsAll iv268.hi (iv268.p.getD 1 dPrm) (iv268.d.getD 1 [])) = true := by
  decide +kernel

theorem iv268_c2 : below iv268.lo (caseIII1Q (lookDT treeK) admPre strsAll iv268.hi (iv268.p.getD 2 dPrm) (iv268.d.getD 2 [])) = true := by
  decide +kernel

theorem iv268_c3 : below iv268.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv268.hi (iv268.p.getD 3 dPrm) (iv268.d.getD 3 [])) = true := by
  decide +kernel

theorem iv268_c4 : below iv268.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv268.hi (iv268.p.getD 4 dPrm) (iv268.d.getD 4 []) (iv268.d.getD 5 [])) = true := by
  decide +kernel

theorem iv268_ok : checkIv2 (lookDT treeK) admPre strsAll iv268 = true :=
  checkIv2_of_cases _ _ _ iv268 rfl rfl (by decide +kernel) iv268_c0 iv268_c1 iv268_c2 iv268_c3 iv268_c4

end ErdosComp
