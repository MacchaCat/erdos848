import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv248_c0 : below iv248.lo (caseIbQ (lookDT treeK) strsAll iv248.hi (iv248.p.getD 0 dPrm) (iv248.d.getD 0 [])) = true := by
  decide +kernel

theorem iv248_c1 : below iv248.lo (caseIIQ (lookDT treeK) admPre strsAll iv248.hi (iv248.p.getD 1 dPrm) (iv248.d.getD 1 [])) = true := by
  decide +kernel

theorem iv248_c2 : below iv248.lo (caseIII1Q (lookDT treeK) admPre strsAll iv248.hi (iv248.p.getD 2 dPrm) (iv248.d.getD 2 [])) = true := by
  decide +kernel

theorem iv248_c3 : below iv248.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv248.hi (iv248.p.getD 3 dPrm) (iv248.d.getD 3 [])) = true := by
  decide +kernel

theorem iv248_c4 : below iv248.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv248.hi (iv248.p.getD 4 dPrm) (iv248.d.getD 4 []) (iv248.d.getD 5 [])) = true := by
  decide +kernel

theorem iv248_ok : checkIv2 (lookDT treeK) admPre strsAll iv248 = true :=
  checkIv2_of_cases _ _ _ iv248 rfl rfl (by decide +kernel) iv248_c0 iv248_c1 iv248_c2 iv248_c3 iv248_c4

end ErdosComp
