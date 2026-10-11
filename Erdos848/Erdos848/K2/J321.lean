import ErdosComp.C2Iv
import ErdosComp.TabK
import ErdosComp.Check2Split

namespace ErdosComp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem iv321_c0 : below iv321.lo (caseIbQ (lookDT treeK) strsAll iv321.hi (iv321.p.getD 0 dPrm) (iv321.d.getD 0 [])) = true := by
  decide +kernel

theorem iv321_c1 : below iv321.lo (caseIIQ (lookDT treeK) admPre strsAll iv321.hi (iv321.p.getD 1 dPrm) (iv321.d.getD 1 [])) = true := by
  decide +kernel

theorem iv321_c2 : below iv321.lo (caseIII1Q (lookDT treeK) admPre strsAll iv321.hi (iv321.p.getD 2 dPrm) (iv321.d.getD 2 [])) = true := by
  decide +kernel

theorem iv321_c3 : below iv321.lo (caseIII2bQ (lookDT treeK) admPre strsAll iv321.hi (iv321.p.getD 3 dPrm) (iv321.d.getD 3 [])) = true := by
  decide +kernel

theorem iv321_c4 : below iv321.lo (caseIII2aQ (lookDT treeK) admPre strsAll iv321.hi (iv321.p.getD 4 dPrm) (iv321.d.getD 4 []) (iv321.d.getD 5 [])) = true := by
  decide +kernel

theorem iv321_ok : checkIv2 (lookDT treeK) admPre strsAll iv321 = true :=
  checkIv2_of_cases _ _ _ iv321 rfl rfl (by decide +kernel) iv321_c0 iv321_c1 iv321_c2 iv321_c3 iv321_c4

end ErdosComp
