import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv290_c0 : below iv290.lo (caseIbQ (lookDT treeK) strsAll iv290.hi (iv290.p.getD 0 dPrm) (iv290.d.getD 0 [])) = true := by
  decide +kernel

theorem iv290_c1 : below iv290.lo (caseIIQ (lookDT treeK) admPre strsAll iv290.hi (iv290.p.getD 1 dPrm) (iv290.d.getD 1 [])) = true := by
  decide +kernel

theorem iv290_c2 : below iv290.lo (caseIII1Q (lookDT treeK) admPre strsAll iv290.hi (iv290.p.getD 2 dPrm) (iv290.d.getD 2 [])) = true := by
  decide +kernel

theorem iv290_c3 : below iv290.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv290.hi (iv290.p.getD 3 dPrm) (iv290.d.getD 3 [])) = true := by
  decide +kernel

theorem iv290_c4 : below iv290.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv290.hi (iv290.p.getD 4 dPrm) (iv290.d.getD 4 []) (iv290.d.getD 5 [])) = true := by
  decide +kernel

theorem iv290_ok : checkIv2 (lookDT treeK) admPre strsAll iv290 = true :=
  checkIv2_of_cases _ _ _ iv290 rfl rfl (by decide +kernel) iv290_c0 iv290_c1 iv290_c2 iv290_c3 iv290_c4

end ErdosComp
