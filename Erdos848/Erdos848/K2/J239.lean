import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv239_c0 : below iv239.lo (caseIbQ (lookDT treeK) strsAll iv239.hi (iv239.p.getD 0 dPrm) (iv239.d.getD 0 [])) = true := by
  decide +kernel

theorem iv239_c1 : below iv239.lo (caseIIQ (lookDT treeK) admPre strsAll iv239.hi (iv239.p.getD 1 dPrm) (iv239.d.getD 1 [])) = true := by
  decide +kernel

theorem iv239_c2 : below iv239.lo (caseIII1Q (lookDT treeK) admPre strsAll iv239.hi (iv239.p.getD 2 dPrm) (iv239.d.getD 2 [])) = true := by
  decide +kernel

theorem iv239_c3 : below iv239.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv239.hi (iv239.p.getD 3 dPrm) (iv239.d.getD 3 [])) = true := by
  decide +kernel

theorem iv239_c4 : below iv239.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv239.hi (iv239.p.getD 4 dPrm) (iv239.d.getD 4 []) (iv239.d.getD 5 [])) = true := by
  decide +kernel

theorem iv239_ok : checkIv2 (lookDT treeK) admPre strsAll iv239 = true :=
  checkIv2_of_cases _ _ _ iv239 rfl rfl (by decide +kernel) iv239_c0 iv239_c1 iv239_c2 iv239_c3 iv239_c4

end ErdosComp
