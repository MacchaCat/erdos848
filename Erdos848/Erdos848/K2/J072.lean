import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv72_c0 : below iv72.lo (caseIbQ (lookDT treeK) strsAll iv72.hi (iv72.p.getD 0 dPrm) (iv72.d.getD 0 [])) = true := by
  decide +kernel

theorem iv72_c1 : below iv72.lo (caseIIQ (lookDT treeK) admPre strsAll iv72.hi (iv72.p.getD 1 dPrm) (iv72.d.getD 1 [])) = true := by
  decide +kernel

theorem iv72_c2 : below iv72.lo (caseIII1Q (lookDT treeK) admPre strsAll iv72.hi (iv72.p.getD 2 dPrm) (iv72.d.getD 2 [])) = true := by
  decide +kernel

theorem iv72_c3 : below iv72.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv72.hi (iv72.p.getD 3 dPrm) (iv72.d.getD 3 [])) = true := by
  decide +kernel

theorem iv72_c4 : below iv72.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv72.hi (iv72.p.getD 4 dPrm) (iv72.d.getD 4 []) (iv72.d.getD 5 [])) = true := by
  decide +kernel

theorem iv72_ok : checkIv2 (lookDT treeK) admPre strsAll iv72 = true :=
  checkIv2_of_cases _ _ _ iv72 rfl rfl (by decide +kernel) iv72_c0 iv72_c1 iv72_c2 iv72_c3 iv72_c4

end ErdosComp
