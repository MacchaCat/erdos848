import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv159_c0 : below iv159.lo (caseIbQ (lookDT treeK) strsAll iv159.hi (iv159.p.getD 0 dPrm) (iv159.d.getD 0 [])) = true := by
  decide +kernel

theorem iv159_c1 : below iv159.lo (caseIIQ (lookDT treeK) admPre strsAll iv159.hi (iv159.p.getD 1 dPrm) (iv159.d.getD 1 [])) = true := by
  decide +kernel

theorem iv159_c2 : below iv159.lo (caseIII1Q (lookDT treeK) admPre strsAll iv159.hi (iv159.p.getD 2 dPrm) (iv159.d.getD 2 [])) = true := by
  decide +kernel

theorem iv159_c3 : below iv159.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv159.hi (iv159.p.getD 3 dPrm) (iv159.d.getD 3 [])) = true := by
  decide +kernel

theorem iv159_c4 : below iv159.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv159.hi (iv159.p.getD 4 dPrm) (iv159.d.getD 4 []) (iv159.d.getD 5 [])) = true := by
  decide +kernel

theorem iv159_ok : checkIv2 (lookDT treeK) admPre strsAll iv159 = true :=
  checkIv2_of_cases _ _ _ iv159 rfl rfl (by decide +kernel) iv159_c0 iv159_c1 iv159_c2 iv159_c3 iv159_c4

end ErdosComp
