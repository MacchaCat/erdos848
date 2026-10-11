import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv128_c0 : below iv128.lo (caseIbQ (lookDT treeK) strsAll iv128.hi (iv128.p.getD 0 dPrm) (iv128.d.getD 0 [])) = true := by
  decide +kernel

theorem iv128_c1 : below iv128.lo (caseIIQ (lookDT treeK) admPre strsAll iv128.hi (iv128.p.getD 1 dPrm) (iv128.d.getD 1 [])) = true := by
  decide +kernel

theorem iv128_c2 : below iv128.lo (caseIII1Q (lookDT treeK) admPre strsAll iv128.hi (iv128.p.getD 2 dPrm) (iv128.d.getD 2 [])) = true := by
  decide +kernel

theorem iv128_c3 : below iv128.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv128.hi (iv128.p.getD 3 dPrm) (iv128.d.getD 3 [])) = true := by
  decide +kernel

theorem iv128_c4 : below iv128.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv128.hi (iv128.p.getD 4 dPrm) (iv128.d.getD 4 []) (iv128.d.getD 5 [])) = true := by
  decide +kernel

theorem iv128_ok : checkIv2 (lookDT treeK) admPre strsAll iv128 = true :=
  checkIv2_of_cases _ _ _ iv128 rfl rfl (by decide +kernel) iv128_c0 iv128_c1 iv128_c2 iv128_c3 iv128_c4

end ErdosComp
