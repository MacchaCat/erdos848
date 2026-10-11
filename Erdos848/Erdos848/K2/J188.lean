import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv188_c0 : below iv188.lo (caseIbQ (lookDT treeK) strsAll iv188.hi (iv188.p.getD 0 dPrm) (iv188.d.getD 0 [])) = true := by
  decide +kernel

theorem iv188_c1 : below iv188.lo (caseIIQ (lookDT treeK) admPre strsAll iv188.hi (iv188.p.getD 1 dPrm) (iv188.d.getD 1 [])) = true := by
  decide +kernel

theorem iv188_c2 : below iv188.lo (caseIII1Q (lookDT treeK) admPre strsAll iv188.hi (iv188.p.getD 2 dPrm) (iv188.d.getD 2 [])) = true := by
  decide +kernel

theorem iv188_c3 : below iv188.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv188.hi (iv188.p.getD 3 dPrm) (iv188.d.getD 3 [])) = true := by
  decide +kernel

theorem iv188_c4 : below iv188.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv188.hi (iv188.p.getD 4 dPrm) (iv188.d.getD 4 []) (iv188.d.getD 5 [])) = true := by
  decide +kernel

theorem iv188_ok : checkIv2 (lookDT treeK) admPre strsAll iv188 = true :=
  checkIv2_of_cases _ _ _ iv188 rfl rfl (by decide +kernel) iv188_c0 iv188_c1 iv188_c2 iv188_c3 iv188_c4

end ErdosComp
