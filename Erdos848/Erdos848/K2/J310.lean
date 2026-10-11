import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv310_c0 : below iv310.lo (caseIbQ (lookDT treeK) strsAll iv310.hi (iv310.p.getD 0 dPrm) (iv310.d.getD 0 [])) = true := by
  decide +kernel

theorem iv310_c1 : below iv310.lo (caseIIQ (lookDT treeK) admPre strsAll iv310.hi (iv310.p.getD 1 dPrm) (iv310.d.getD 1 [])) = true := by
  decide +kernel

theorem iv310_c2 : below iv310.lo (caseIII1Q (lookDT treeK) admPre strsAll iv310.hi (iv310.p.getD 2 dPrm) (iv310.d.getD 2 [])) = true := by
  decide +kernel

theorem iv310_c3 : below iv310.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv310.hi (iv310.p.getD 3 dPrm) (iv310.d.getD 3 [])) = true := by
  decide +kernel

theorem iv310_c4 : below iv310.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv310.hi (iv310.p.getD 4 dPrm) (iv310.d.getD 4 []) (iv310.d.getD 5 [])) = true := by
  decide +kernel

theorem iv310_ok : checkIv2 (lookDT treeK) admPre strsAll iv310 = true :=
  checkIv2_of_cases _ _ _ iv310 rfl rfl (by decide +kernel) iv310_c0 iv310_c1 iv310_c2 iv310_c3 iv310_c4

end ErdosComp
